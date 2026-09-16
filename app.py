"""日本株・海外株の株価と大調整後の底練りを分析する標準ライブラリ製アプリ。"""

from __future__ import annotations

import json
import math
import re
import sqlite3
import sys
import threading
import time
import uuid
import webbrowser
import contextvars
import csv
import io
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass, replace
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from statistics import mean
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, urlparse
from urllib.request import Request, urlopen


APP_HOST = "127.0.0.1"
START_PORT = 8765
APP_DIRECTORY = Path(__file__).resolve().parent
DATABASE_PATH = str(APP_DIRECTORY / "stock_cache.db")
ALGORITHM_VERSION = "5.3-long-general-history"
INCREMENTAL_OVERLAP_DAYS = 14

# 底練り判定の設定。後から検証結果に応じて調整しやすいよう、一か所に集約する。
VOLATILITY_WINDOW = 20
INITIAL_VOLATILITY_DAYS = 40
SIDEWAYS_WINDOW = 60
SHORT_MA_DAYS = 25
LONG_MA_DAYS = 75
MA_SLOPE_DAYS = 20
FIRST_YEAR_CALENDAR_DAYS = 365
PEAK_PRICE_RATIO_LIMIT = 0.50
VOLATILITY_ABS_RETURN_LIMIT = 3.0
IDEAL_RANGE_WIDTH = 20.0
RANGE_WIDTH_LIMIT = 30.0
STABILITY_SCORE_THRESHOLD = 75
SETUP_LOOKBACK_DAYS = 20
SETUP_DENSITY_WINDOW = 15
SETUP_REQUIRED_DAYS = 10
BREAKOUT_WINDOW = 60
EXPANSION_BREAKOUT_WINDOW = 20
BREAKOUT_BUFFER_PERCENT = 1.0
BREAKOUT_MIN_RETURN_PERCENT = 2.0
EXPANSION_RETURN_PERCENT = 5.0
BREAKOUT_VOLUME_RATIO = 1.5
EXPANSION_VOLUME_RATIO = 2.0
CLOSE_STRENGTH_LIMIT = 0.65
TRIGGER_CONFIRM_DAYS = 2
BREAKOUT_HOLD_TOLERANCE = 0.98
ANALYSIS_MAX_YEARS = 5
MIN_ANALYSIS_DAYS = LONG_MA_DAYS + MA_SLOPE_DAYS
MAX_BATCH_WORKERS = 3
BATCH_JOBS: dict[str, dict] = {}
BATCH_JOBS_LOCK = threading.Lock()
CURRENT_BATCH_TIMINGS: contextvars.ContextVar[dict | None] = contextvars.ContextVar(
    "CURRENT_BATCH_TIMINGS",
    default=None,
)
DEFAULT_DELAYED_BUY_DAYS = 106
DEFAULT_DRAWDOWN_BUY_PERCENT = -20.0
BENCHMARK_SYMBOL = "ACWI"
BENCHMARK_LABEL = "オルカン相当"
IMPORTANT_EVENT_LOOKBACK_DAYS = 75
IMPORTANT_EVENT_REFRESH_HOURS = 20
IMPORTANT_EVENT_MOVE_THRESHOLD = 12.0
IMPORTANT_EVENT_VOLUME_THRESHOLD = 2.0
IMPORTANT_DISCLOSURE_KEYWORDS = (
    "決算短信",
    "四半期決算",
    "決算説明",
    "業績予想",
    "業績予測",
    "通期業績",
    "上方修正",
    "下方修正",
    "修正",
    "配当予想",
)
KNOWN_IMPORTANT_EVENTS = {
    "285A.T": [
        ("2024-12-18", "東証プライム上場", "上場"),
        ("2025-02-14", "2025年3月期 第3四半期決算", "決算"),
        ("2025-05-15", "2025年3月期 通期決算", "決算"),
        ("2025-08-08", "2026年3月期 第1四半期決算", "決算"),
        ("2025-11-13", "2026年3月期 第2四半期決算", "決算"),
        ("2026-02-12", "2026年3月期 第3四半期決算・通期予想", "決算"),
        ("2026-05-15", "2026年3月期 通期決算・次期予想", "決算"),
    ],
}


@dataclass(frozen=True)
class SignalConfig:
    peak_window: int = 500
    min_peak_history: int = 120
    stock_drawdown_percent: float = 40.0
    etf_drawdown_percent: float = 25.0
    recent_low_drawdown_percent: float = 45.0
    stock_min_peak_age: int = 120
    etf_min_peak_age: int = 80
    range_window: int = 60
    ideal_range_percent: float = 20.0
    max_range_percent: float = 30.0
    volatility_window: int = 20
    max_abs_return_percent: float = 2.5
    setup_density_window: int = 15
    setup_required_days: int = 10
    setup_lookback_days: int = 20
    breakout_window: int = 60
    expansion_window: int = 20
    breakout_buffer_percent: float = 1.0
    breakout_min_return_percent: float = 2.0
    expansion_return_percent: float = 5.0
    breakout_volume_ratio: float = 1.5
    expansion_volume_ratio: float = 2.0
    close_strength_limit: float = 0.65
    confirmation_days: int = 2
    hold_tolerance: float = 0.98
    cooldown_days: int = 60
    forward_windows: tuple[int, ...] = (5, 20, 60)


DEFAULT_SIGNAL_CONFIG = SignalConfig()
ALGORITHM_MODES = {"general", "ipo"}

MARKET_SUFFIXES = {
    "auto": "",
    "japan": ".T",
    "usa": "",
    "uk": ".L",
    "germany": ".DE",
    "hongkong": ".HK",
}
SYMBOL_SEARCH_SEEDS = [
    {"symbol": "285A.T", "name": "キオクシア / KIOXIA", "market": "日本"},
    {"symbol": "4385.T", "name": "メルカリ", "market": "日本"},
    {"symbol": "7974.T", "name": "任天堂", "market": "日本"},
    {"symbol": "8136.T", "name": "サンリオ", "market": "日本"},
    {"symbol": "8035.T", "name": "東京エレクトロン", "market": "日本"},
    {"symbol": "6920.T", "name": "レーザーテック", "market": "日本"},
    {"symbol": "2413.T", "name": "M3 / エムスリー", "market": "日本"},
    {"symbol": "4477.T", "name": "BASE", "market": "日本"},
    {"symbol": "9348.T", "name": "ispace", "market": "日本"},
    {"symbol": "6098.T", "name": "リクルート", "market": "日本"},
    {"symbol": "7203.T", "name": "トヨタ自動車", "market": "日本"},
    {"symbol": "6758.T", "name": "ソニーグループ", "market": "日本"},
    {"symbol": "MSFT", "name": "Microsoft", "market": "米国"},
    {"symbol": "AAPL", "name": "Apple", "market": "米国"},
    {"symbol": "NVDA", "name": "NVIDIA", "market": "米国"},
    {"symbol": "AMD", "name": "AMD", "market": "米国"},
    {"symbol": "ASML", "name": "ASML", "market": "米国"},
    {"symbol": "QQQ", "name": "NASDAQ 100 ETF", "market": "米国ETF"},
    {"symbol": "SOXX", "name": "半導体ETF / iShares Semiconductor ETF", "market": "米国ETF"},
]

SYMBOL_SEARCH_ALIASES = {
    "285A.T": ["285A", "KIOXIA", "キオクシア", "きおくしあ"],
    "4385.T": ["4385", "メルカリ", "MERCARI"],
    "7974.T": ["7974", "任天堂", "ニンテンドー", "NINTENDO"],
    "8136.T": ["8136", "サンリオ", "SANRIO"],
    "8035.T": ["8035", "東京エレクトロン", "東エレク", "TEL", "TOKYO ELECTRON"],
    "6920.T": ["6920", "レーザーテック", "LASERTEC"],
    "6857.T": ["6857", "アドバンテスト", "ADVANTEST"],
    "6146.T": ["6146", "ディスコ", "DISCO"],
    "7735.T": ["7735", "SCREEN", "スクリーン"],
    "7203.T": ["7203", "トヨタ", "TOYOTA"],
    "6758.T": ["6758", "ソニー", "SONY"],
    "9984.T": ["9984", "ソフトバンクグループ", "SOFTBANK"],
    "9983.T": ["9983", "ファーストリテイリング", "ユニクロ", "FAST RETAILING"],
    "6098.T": ["6098", "リクルート", "RECRUIT"],
    "AAPL": ["APPLE", "アップル", "AAPL"],
    "MSFT": ["MICROSOFT", "マイクロソフト", "MSFT"],
    "NVDA": ["NVIDIA", "エヌビディア", "NVDA"],
    "AMD": ["AMD"],
    "ASML": ["ASML"],
    "QQQ": ["QQQ", "NASDAQ", "ナスダック"],
    "VOO": ["VOO", "S&P500", "SP500"],
    "SOXX": ["SOXX", "半導体ETF", "SEMICONDUCTOR ETF"],
}

JAPAN_LARGE_CAP_UNIVERSE = [
    "7203", "8306", "6758", "6861", "8035", "9983", "9984", "8316", "9432",
    "9433", "7974", "4063", "6098", "4568", "8058", "8001", "8031", "8766",
    "8411", "7267", "6902", "7741", "6501", "6594", "6702", "2914", "4519",
    "4502", "4578", "4503", "6954", "6981", "6273", "6146", "6857", "7735",
    "6920", "6723", "6752", "7751", "4901", "5108", "8801", "8802", "9020",
    "9021", "9022", "9201", "9202", "3382", "8267", "9843", "4661", "9735",
    "4689", "4755", "3659", "2413", "4385", "4477", "6095", "2127", "3697",
    "4704", "4307", "4684", "9613", "9697", "6701", "6703", "6503", "6504",
    "6506", "6367", "6326", "6301", "6305", "7011", "7012", "7013", "7201",
    "7261", "7269", "7270", "7211", "7202", "7205", "7272", "5101", "5110",
    "5401", "5411", "5406", "3436", "5713", "5711", "5801", "5802", "5803",
    "1605", "5020", "5019", "5021", "3402", "3407", "4005", "4188", "4183",
    "4204", "4452", "4911", "4922", "2502", "2503", "2587", "2801", "2802",
    "2871", "2897", "2269", "2282", "2267", "1332", "2002", "3861", "1925",
    "1928", "1801", "1802", "1803", "1812", "1808", "1878", "3401", "3405",
    "7014", "7276", "3110", "2768", "3086", "3092", "3099", "3141", "3197",
    "8233", "8252", "8273", "9989", "2670", "7532", "7550", "8227", "8591",
    "8593", "8601", "8604", "8630", "8725", "8750", "8795", "8308", "8309",
    "8331", "8354", "8359", "7182", "7186", "7167", "8473", "8253", "3289",
    "3231", "3291", "8951", "8952", "8972", "9147", "9101", "9104", "9107",
    "9042", "9005", "9007", "9008", "9009", "9024", "9143", "9064", "9065",
    "9142", "9501", "9502", "9503", "9531", "9532", "9533", "9513", "9508",
    "9509", "9506", "9504", "9507", "4612", "5332", "5333", "5201", "5233",
    "5214", "5334", "7731", "7733", "7747", "4543", "4523", "4528", "4536",
    "4544", "4887", "6323", "6460", "6471", "6472", "6473", "6479", "6481",
    "6645", "6762", "6770", "6841", "6845", "6963", "6965", "6971", "6976",
    "6988", "7745", "7752", "7762", "7832", "7951", "8113", "8136",
]

US_LARGE_CAP_UNIVERSE = [
    "AAPL", "MSFT", "NVDA", "AMZN", "GOOGL", "GOOG", "META", "TSLA", "AVGO",
    "BRK-B", "LLY", "JPM", "V", "UNH", "XOM", "MA", "COST", "WMT", "HD",
    "PG", "JNJ", "ORCL", "ABBV", "BAC", "KO", "NFLX", "CRM", "CVX", "MRK",
    "AMD", "PEP", "ADBE", "TMO", "LIN", "ACN", "MCD", "CSCO", "ABT", "WFC",
    "IBM", "QCOM", "GE", "TXN", "AMGN", "INTU", "NOW", "DHR", "PM", "CAT",
    "VZ", "ISRG", "NEE", "PFE", "RTX", "SPGI", "UBER", "GS", "AXP", "LOW",
    "BKNG", "HON", "MS", "T", "BLK", "UNP", "PGR", "SYK", "LMT", "TJX",
    "ELV", "VRTX", "C", "ETN", "MDT", "SCHW", "BSX", "CB", "AMAT", "ADI",
    "PANW", "DE", "ADP", "MU", "FI", "GILD", "COP", "MMC", "PLD", "SBUX",
    "KLAC", "LRCX", "INTC", "BA", "UPS", "NKE", "MDLZ", "SO", "DUK", "MO",
    "CL", "ICE", "EQIX", "SHW", "REGN", "ZTS", "APH", "CDNS", "SNPS", "MCK",
    "WM", "CMG", "ORLY", "TDG", "EOG", "USB", "PNC", "APD", "FDX", "EMR",
    "ITW", "HCA", "AON", "MAR", "ROP", "NXPI", "FTNT", "CRWD", "COIN", "PLTR",
]

SEMICONDUCTOR_UNIVERSE = [
    "285A", "8035", "6920", "6857", "6146", "7735", "6723", "6752", "6501",
    "6701", "6702", "3436", "4063", "4186", "4188", "5801", "5802", "5803",
    "6315", "6323", "6383", "6525", "6526", "6622", "6627", "6728", "6762",
    "6770", "6841", "6845", "6871", "6875", "6890", "6963", "6965", "6971",
    "6976", "6981", "6988", "7745", "7751", "8031", "8058", "NVDA", "AMD",
    "AVGO", "QCOM", "TXN", "MU", "INTC", "AMAT", "LRCX", "KLAC", "ADI", "NXPI",
    "ON", "MCHP", "MRVL", "MPWR", "TER", "ASML", "TSM", "ARM", "SOXX", "SMH",
]

TSE_GROWTH_UNIVERSE = [
    "130A", "137A", "141A", "143A", "145A", "147A", "148A", "149A", "153A",
    "155A", "156A", "157A", "166A", "168A", "175A", "176A", "177A", "184A",
    "186A", "190A", "192A", "194A", "195A", "196A", "197A", "198A", "199A",
    "200A", "201A", "202A", "203A", "205A", "206A", "207A", "208A", "209A",
    "211A", "212A", "213A", "214A", "215A", "216A", "217A", "218A", "219A",
    "220A", "221A", "222A", "223A", "224A", "225A", "226A", "228A", "229A",
    "230A", "231A", "232A", "233A", "234A", "235A", "236A", "237A", "238A",
    "239A", "240A", "241A", "242A", "243A", "244A", "245A", "246A", "247A",
    "248A", "249A", "250A", "251A", "252A", "253A", "254A", "255A", "256A",
    "257A", "258A", "259A", "260A", "261A", "262A", "263A", "264A", "265A",
    "266A", "267A", "268A", "269A", "270A", "271A", "272A", "274A", "276A",
    "277A", "278A", "279A", "280A", "281A", "282A", "283A", "285A", "286A",
    "288A", "289A", "290A", "291A", "292A", "293A", "294A", "295A", "296A",
    "297A", "298A", "299A", "300A", "302A", "303A", "304A", "305A", "306A",
    "307A", "308A", "309A", "310A", "311A", "313A", "314A", "315A", "316A",
    "318A", "319A", "320A", "321A", "322A", "323A", "324A", "325A", "326A",
    "327A", "328A", "330A", "331A", "332A", "334A", "335A", "336A", "337A",
    "338A", "339A", "340A", "341A", "342A", "343A", "344A", "345A", "347A",
    "348A", "349A", "350A", "354A", "355A", "356A", "357A", "358A", "359A",
    "362A", "363A", "364A", "365A", "366A", "367A", "368A", "369A", "371A",
    "372A", "373A", "374A", "376A", "377A", "378A", "379A", "380A", "381A",
    "382A", "383A", "384A", "385A", "386A", "390A", "391A", "392A", "393A",
    "394A", "395A", "396A", "397A", "398A", "399A", "4011", "4051", "4052",
    "4053", "4054", "4055", "4056", "4057", "4058", "4059", "4060", "4068",
    "4071", "4073", "4074", "4075", "4076", "4078", "4165", "4166", "4167",
    "4168", "4169", "4170", "4171", "4172", "4173", "4174", "4175", "4176",
    "4177", "4178", "4179", "4192", "4193", "4194", "4196", "4197", "4255",
    "4256", "4258", "4259", "4260", "4261", "4262", "4263", "4264", "4265",
    "4267", "4268", "4269", "4270", "4370", "4371", "4372", "4373", "4374",
    "4375", "4376", "4377", "4378", "4379", "4380", "4381", "4382", "4384",
    "4385", "4386", "4387", "4388", "4389", "4390", "4391", "4392", "4393",
    "4394", "4395", "4397", "4412", "4413", "4414", "4415", "4416", "4417",
    "4418", "4419", "4420", "4422", "4424", "4425", "4427", "4428", "4431",
    "4434", "4435", "4436", "4438", "4439", "4442", "4443", "4444", "4445",
    "4446", "4447", "4448", "4449", "4475", "4476", "4477", "4478", "4479",
    "4480", "4481", "4482", "4483", "4484", "4485", "4486", "4487", "4488",
    "4489", "4490", "4491", "4492", "4493", "4494", "4495", "4496", "4498",
    "4880", "4881", "4882", "4883", "4884", "4888", "4890", "4891", "4892",
    "4893", "4894", "4896", "4897", "5025", "5026", "5027", "5028", "5029",
    "5031", "5032", "5033", "5034", "5035", "5036", "5038", "5125", "5126",
    "5127", "5129", "5131", "5132", "5134", "5136", "5137", "5138", "5139",
    "5240", "5242", "5243", "5244", "5246", "5247", "5248", "5250", "5252",
    "5253", "5254", "5255", "5256", "5257", "5258", "5259", "5570", "5571",
    "5572", "5574", "5575", "5576", "5577", "5578", "5579", "5580", "5582",
    "5585", "5586", "5587", "5588", "5589", "5590", "5591", "5592", "5595",
    "5596", "5597", "5599", "5616", "5618", "5621", "5834", "5836", "5842",
    "5845", "5848", "5858", "5867", "5870", "5871", "5884", "5885", "5888",
    "5891", "6027", "6030", "6031", "6033", "6034", "6038", "6040", "6045",
    "6046", "6047", "6048", "6049", "6050", "6069", "6072", "6079", "6081",
    "6085", "6086", "6088", "6090", "6092", "6094", "6095", "6096", "6098",
    "6166", "6172", "6173", "6176", "6177", "6190", "6191", "6192", "6193",
    "6194", "6195", "6198", "6232", "6521", "6522", "6524", "6525", "6526",
    "6527", "6550", "6551", "6552", "6554", "6555", "6556", "6557", "6558",
    "6573", "6574", "6577", "6578", "6579", "6580", "6612", "6613", "6614",
    "6618", "7041", "7042", "7043", "7044", "7046", "7047", "7048", "7049",
    "7050", "7059", "7060", "7061", "7062", "7063", "7064", "7065", "7066",
    "7067", "7068", "7069", "7071", "7072", "7073", "7074", "7077", "7078",
    "7079", "7080", "7082", "7083", "7084", "7086", "7088", "7090", "7091",
    "7093", "7094", "7095", "7096", "7097", "7098", "7099", "7110", "7112",
    "7114", "7115", "7116", "7118", "7119", "7133", "7138", "7140", "7157",
    "7317", "7320", "7325", "7342", "7343", "7345", "7347", "7351", "7352",
    "7353", "7354", "7356", "7359", "7360", "7361", "7362", "7363", "7366",
    "7367", "7368", "7370", "7371", "7372", "7373", "7374", "7375", "7376",
    "7378", "7379", "7792", "7793", "7794", "7795", "7796", "9211", "9212",
    "9213", "9214", "9215", "9216", "9218", "9219", "9221", "9223", "9225",
    "9227", "9229", "9235", "9236", "9237", "9238", "9239", "9240", "9241",
    "9242", "9244", "9245", "9246", "9247", "9248", "9250", "9251", "9252",
    "9253", "9254", "9256", "9257", "9258", "9259", "9270", "9330", "9331",
    "9336", "9337", "9338", "9339", "9340", "9341", "9342", "9343", "9344",
    "9345", "9346", "9347", "9348", "9349", "9552", "9553", "9554", "9556",
    "9557", "9558", "9560", "9561", "9562", "9563", "9565",
]

NASDAQ100_UNIVERSE = [
    "AAPL", "MSFT", "NVDA", "AMZN", "AVGO", "META", "GOOGL", "GOOG", "TSLA",
    "COST", "NFLX", "ASML", "TMUS", "CSCO", "AMD", "AZN", "LIN", "PEP", "ADBE",
    "ISRG", "QCOM", "TXN", "INTU", "AMGN", "AMAT", "BKNG", "HON", "PDD", "CMCSA",
    "VRTX", "SBUX", "GILD", "PANW", "ADP", "MU", "ADI", "MELI", "LRCX", "KLAC",
    "SNPS", "CDNS", "CRWD", "MAR", "REGN", "CEG", "MDLZ", "CTAS", "ORLY",
    "DASH", "FTNT", "CSX", "ABNB", "ADSK", "PYPL", "ROP", "NXPI", "PCAR", "WDAY",
    "PAYX", "MNST", "MRVL", "AEP", "ROST", "CPRT", "KDP", "FAST", "FANG",
    "KHC", "EXC", "CHTR", "GEHC", "TTWO", "IDXX", "EA", "DDOG", "ODFL", "BKR",
    "VRSK", "CTSH", "XEL", "CSGP", "ON", "TEAM", "CCEP", "ZS", "DXCM", "LULU",
    "BIIB", "MDB", "MCHP", "ANSS", "GFS", "CDW", "WBD", "ILMN", "MRNA", "DLTR",
    "SIRI", "WBA",
]

SOX_SEMICONDUCTOR_EXTENDED_UNIVERSE = [
    "SOXX|ETF", "SMH|ETF", "SOXL|ETF", "SOXS|ETF", "NVDA", "AMD", "AVGO", "QCOM",
    "TXN", "MU", "INTC", "AMAT", "LRCX", "KLAC", "ADI", "NXPI", "ON", "MCHP",
    "MRVL", "MPWR", "TER", "ASML", "TSM", "ARM", "GFS", "COHR", "ENTG", "MKSI",
    "ACLS", "AEHR", "AMBA", "FORM", "LSCC", "MTSI", "POWI", "RMBS", "SMTC",
    "SWKS", "SYNA", "TSEM", "UCTT", "VECO", "WOLF", "ACMR", "ALGM", "AMKR",
    "ASX", "CAMT", "CRUS", "DIOD", "IMOS", "IPGP", "KLIC", "NVTS", "PI", "SIMO",
    "SLAB", "STM", "UMC", "WDC", "285A", "8035", "6920", "6857", "6146", "7735",
    "6723", "6752", "6501", "6701", "6702", "3436", "4063", "4186", "4188",
    "5801", "5802", "5803", "6315", "6323", "6383", "6525", "6526", "6622",
    "6627", "6728", "6762", "6770", "6841", "6845", "6871", "6875", "6890",
    "6963", "6965", "6971", "6976", "6981", "6988", "7745", "7751", "8031",
    "8058",
]

ETF_COMMODITY_UNIVERSE = [
    "VOO|ETF", "SPY|ETF", "IVV|ETF", "QQQ|ETF", "DIA|ETF", "IWM|ETF", "VT|ETF",
    "VTI|ETF", "VEA|ETF", "VWO|ETF", "ACWI|ETF", "SOXX|ETF", "SMH|ETF",
    "XLK|ETF", "XLY|ETF", "XLC|ETF", "XLF|ETF", "XLE|ETF", "XLV|ETF", "XLI|ETF",
    "XLP|ETF", "XLU|ETF", "XLB|ETF", "XLRE|ETF", "GLD|ETF", "IAU|ETF",
    "GDX|ETF", "GDXJ|ETF", "SLV|ETF", "PPLT|ETF", "PALL|ETF", "USO|ETF",
    "UNG|ETF", "DBA|ETF", "DBC|ETF", "CORN|ETF", "WEAT|ETF", "SOYB|ETF",
    "TLT|ETF", "IEF|ETF", "SHY|ETF", "HYG|ETF", "LQD|ETF", "TIP|ETF",
    "UUP|ETF", "FXY|ETF", "FXE|ETF", "FXB|ETF", "FXA|ETF", "BTC-USD|ETF",
    "ETH-USD|ETF", "^GSPC|ETF", "^IXIC|ETF", "^DJI|ETF", "^RUT|ETF", "^SOX|ETF",
    "^N225|ETF", "^TOPX|ETF", "GC=F|ETF", "SI=F|ETF", "CL=F|ETF", "NG=F|ETF",
]

BATCH_UNIVERSES = {
    "known": [],
    "japan_large": JAPAN_LARGE_CAP_UNIVERSE,
    "us_large": US_LARGE_CAP_UNIVERSE,
    "semiconductor": SEMICONDUCTOR_UNIVERSE,
    "tse_growth": TSE_GROWTH_UNIVERSE,
    "nasdaq100": NASDAQ100_UNIVERSE,
    "sox_semiconductor": SOX_SEMICONDUCTOR_EXTENDED_UNIVERSE,
    "etf_commodity": ETF_COMMODITY_UNIVERSE,
    "all_core": (
        JAPAN_LARGE_CAP_UNIVERSE
        + US_LARGE_CAP_UNIVERSE
        + SEMICONDUCTOR_UNIVERSE
        + TSE_GROWTH_UNIVERSE
        + NASDAQ100_UNIVERSE
        + SOX_SEMICONDUCTOR_EXTENDED_UNIVERSE
        + ETF_COMMODITY_UNIVERSE
    ),
}

PERIODS = {
    "1mo": ("1mo", "1d"),
    "3mo": ("3mo", "1d"),
    "6mo": ("6mo", "1d"),
    "1y": ("1y", "1d"),
    "5y": ("5y", "1wk"),
    "max": ("max", "1mo"),
}


@dataclass(frozen=True)
class PricePoint:
    timestamp: int
    date_text: str
    close: float
    high: float | None
    low: float | None
    volume: int | None = None


@dataclass(frozen=True)
class StockResult:
    symbol: str
    name: str
    currency: str
    exchange: str
    points: list[PricePoint]
    first_trade_timestamp: int | None
    security_type: str = "stock"


@contextmanager
def database_connection():
    connection = sqlite3.connect(DATABASE_PATH, timeout=30)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA journal_mode = WAL")
    try:
        yield connection
        connection.commit()
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def initialize_database() -> None:
    with database_connection() as connection:
        connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS stocks (
                symbol TEXT PRIMARY KEY,
                name TEXT NOT NULL,
                currency TEXT NOT NULL DEFAULT '',
                exchange TEXT NOT NULL DEFAULT '',
                first_trade_timestamp INTEGER,
                listing_date TEXT,
                last_price_date TEXT,
                market_cap REAL,
                market_cap_currency TEXT NOT NULL DEFAULT '',
                market_cap_updated_at TEXT,
                security_type TEXT NOT NULL DEFAULT 'stock',
                history_complete INTEGER NOT NULL DEFAULT 0,
                long_history_complete INTEGER NOT NULL DEFAULT 0,
                updated_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS daily_prices (
                symbol TEXT NOT NULL,
                price_date TEXT NOT NULL,
                timestamp INTEGER NOT NULL,
                close REAL NOT NULL,
                high REAL,
                low REAL,
                volume INTEGER,
                PRIMARY KEY (symbol, price_date),
                FOREIGN KEY (symbol) REFERENCES stocks(symbol) ON DELETE CASCADE
            );

            CREATE INDEX IF NOT EXISTS idx_daily_prices_symbol_timestamp
            ON daily_prices(symbol, timestamp);

            CREATE TABLE IF NOT EXISTS analyses (
                symbol TEXT NOT NULL,
                algorithm_version TEXT NOT NULL,
                detected INTEGER NOT NULL,
                stable_date TEXT,
                calendar_days_to_stable INTEGER,
                score_at_stable REAL,
                analyzed_through TEXT,
                result_json TEXT NOT NULL,
                analyzed_at TEXT NOT NULL,
                PRIMARY KEY (symbol, algorithm_version),
                FOREIGN KEY (symbol) REFERENCES stocks(symbol) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS important_events (
                symbol TEXT NOT NULL,
                event_date TEXT NOT NULL,
                title TEXT NOT NULL,
                category TEXT NOT NULL DEFAULT '',
                source TEXT NOT NULL DEFAULT '',
                url TEXT NOT NULL DEFAULT '',
                fetched_at TEXT NOT NULL,
                PRIMARY KEY (symbol, event_date, title, source),
                FOREIGN KEY (symbol) REFERENCES stocks(symbol) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS important_event_fetch_log (
                symbol TEXT NOT NULL,
                source TEXT NOT NULL,
                fetched_at TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT '',
                message TEXT NOT NULL DEFAULT '',
                PRIMARY KEY (symbol, source)
            );

            CREATE TABLE IF NOT EXISTS market_cap_cache (
                symbol TEXT PRIMARY KEY,
                market_cap REAL NOT NULL,
                currency TEXT NOT NULL DEFAULT '',
                updated_at TEXT NOT NULL
            );
            """
        )
        columns = {
            row["name"]
            for row in connection.execute(
                "PRAGMA table_info(daily_prices)"
            ).fetchall()
        }
        if "volume" not in columns:
            connection.execute(
                "ALTER TABLE daily_prices ADD COLUMN volume INTEGER"
            )
        stock_columns = {
            row["name"]
            for row in connection.execute(
                "PRAGMA table_info(stocks)"
            ).fetchall()
        }
        if "security_type" not in stock_columns:
            connection.execute(
                "ALTER TABLE stocks ADD COLUMN "
                "security_type TEXT NOT NULL DEFAULT 'stock'"
            )
        if "long_history_complete" not in stock_columns:
            connection.execute(
                "ALTER TABLE stocks ADD COLUMN "
                "long_history_complete INTEGER NOT NULL DEFAULT 0"
            )
        if "market_cap" not in stock_columns:
            connection.execute("ALTER TABLE stocks ADD COLUMN market_cap REAL")
        if "market_cap_currency" not in stock_columns:
            connection.execute(
                "ALTER TABLE stocks ADD COLUMN "
                "market_cap_currency TEXT NOT NULL DEFAULT ''"
            )
        if "market_cap_updated_at" not in stock_columns:
            connection.execute(
                "ALTER TABLE stocks ADD COLUMN market_cap_updated_at TEXT"
            )
        connection.execute(
            """
            DELETE FROM market_cap_cache
            WHERE market_cap < 1000000
               OR (symbol LIKE '%.T' AND market_cap < 100000000)
               OR (currency = 'JPY' AND market_cap < 100000000)
            """
        )
        connection.execute(
            """
            UPDATE stocks
            SET market_cap = NULL,
                market_cap_currency = '',
                market_cap_updated_at = NULL
            WHERE market_cap IS NOT NULL
              AND (
                market_cap < 1000000
                OR (symbol LIKE '%.T' AND market_cap < 100000000)
                OR (market_cap_currency = 'JPY' AND market_cap < 100000000)
              )
            """
        )


def utc_now_text() -> str:
    return datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")


@contextmanager
def batch_timing_step(name: str):
    started = time.perf_counter()
    try:
        yield
    finally:
        timings = CURRENT_BATCH_TIMINGS.get()
        if timings is None:
            return
        elapsed = time.perf_counter() - started
        item = timings.setdefault(
            name,
            {
                "name": name,
                "totalSeconds": 0.0,
                "count": 0,
                "maxSeconds": 0.0,
            },
        )
        item["totalSeconds"] += elapsed
        item["count"] += 1
        item["maxSeconds"] = max(item["maxSeconds"], elapsed)


def normalized_timing_items(timings: dict | None) -> list[dict]:
    if not timings:
        return []
    items = []
    for item in timings.values():
        count = int(item.get("count") or 0)
        total = float(item.get("totalSeconds") or 0.0)
        items.append(
            {
                "name": item.get("name") or "",
                "totalSeconds": round(total, 3),
                "count": count,
                "averageSeconds": round(total / count, 3) if count else 0.0,
                "maxSeconds": round(float(item.get("maxSeconds") or 0.0), 3),
            }
        )
    items.sort(key=lambda item: item["totalSeconds"], reverse=True)
    return items


def aggregate_batch_timings(results: list[dict]) -> list[dict]:
    aggregate: dict[str, dict] = {}
    for result in results:
        for item in result.get("timings") or []:
            name = item.get("name") or ""
            if not name:
                continue
            target = aggregate.setdefault(
                name,
                {
                    "name": name,
                    "totalSeconds": 0.0,
                    "count": 0,
                    "maxSeconds": 0.0,
                },
            )
            target["totalSeconds"] += float(item.get("totalSeconds") or 0.0)
            target["count"] += int(item.get("count") or 0)
            target["maxSeconds"] = max(
                target["maxSeconds"],
                float(item.get("maxSeconds") or 0.0),
            )
    return normalized_timing_items(aggregate)


def slowest_batch_symbols(results: list[dict], limit: int = 10) -> list[dict]:
    items = [
        {
            "symbol": result.get("symbol") or result.get("input") or "",
            "name": result.get("name") or "",
            "elapsedSeconds": round(float(result.get("elapsedSeconds") or 0.0), 3),
            "error": result.get("error") or "",
        }
        for result in results
        if result.get("elapsedSeconds") is not None
    ]
    items.sort(key=lambda item: item["elapsedSeconds"], reverse=True)
    return items[:limit]


def analysis_horizon_timestamp(first_trade_timestamp: int) -> int:
    return min(
        int(time.time()) + 86400,
        first_trade_timestamp + int(ANALYSIS_MAX_YEARS * 366 * 86400),
    )


def stock_row(symbol: str) -> sqlite3.Row | None:
    initialize_database()
    with database_connection() as connection:
        return connection.execute(
            "SELECT * FROM stocks WHERE symbol = ?", (symbol,)
        ).fetchone()


def cached_stock_market_cap(symbol: str) -> tuple[float | None, str]:
    initialize_database()
    with database_connection() as connection:
        cache_row = connection.execute(
            """
            SELECT market_cap, currency
            FROM market_cap_cache
            WHERE symbol = ?
            """,
            (symbol,),
        ).fetchone()
    if cache_row is not None:
        try:
            numeric = float(cache_row["market_cap"])
        except (TypeError, ValueError):
            numeric = 0.0
        if is_plausible_market_cap(symbol, numeric, cache_row["currency"] or ""):
            return numeric, cache_row["currency"] or ""
    row = stock_row(symbol)
    if row is None:
        return None, ""
    try:
        value = row["market_cap"]
    except (KeyError, IndexError):
        value = None
    if value is None:
        return None, ""
    try:
        numeric = float(value)
    except (TypeError, ValueError):
        return None, ""
    if not math.isfinite(numeric) or numeric <= 0:
        return None, ""
    currency = ""
    try:
        currency = row["market_cap_currency"] or row["currency"] or ""
    except (KeyError, IndexError):
        currency = ""
    return numeric, currency


def save_stock_market_cap(
    symbol: str,
    market_cap: float | int | None,
    currency: str | None,
) -> None:
    if market_cap is None:
        return
    try:
        numeric = float(market_cap)
    except (TypeError, ValueError):
        return
    if not is_plausible_market_cap(symbol, numeric, currency or ""):
        return
    initialize_database()
    with database_connection() as connection:
        connection.execute(
            """
            INSERT INTO market_cap_cache (
                symbol, market_cap, currency, updated_at
            ) VALUES (?, ?, ?, ?)
            ON CONFLICT(symbol) DO UPDATE SET
                market_cap = excluded.market_cap,
                currency = excluded.currency,
                updated_at = excluded.updated_at
            """,
            (
                symbol,
                numeric,
                currency or "",
                utc_now_text(),
            ),
        )
        connection.execute(
            """
            UPDATE stocks
            SET market_cap = ?,
                market_cap_currency = ?,
                market_cap_updated_at = ?
            WHERE symbol = ?
            """,
            (
                numeric,
                currency or "",
                utc_now_text(),
                symbol,
            ),
        )


def normalize_market_cap_import_symbol(value: str) -> str:
    raw = str(value or "").strip().strip('"').strip("'")
    if not raw:
        raise ValueError("銘柄コードが空です。")
    raw = raw.upper()
    raw = re.sub(r"\s+", "", raw)
    raw = raw.replace("JP:", "").replace("TYO:", "")
    if re.fullmatch(r"\d{4}", raw):
        return f"{raw}.T"
    return normalize_symbol(raw, "auto")


def market_cap_column_value(row: dict, aliases: tuple[str, ...]) -> str:
    normalized = {
        str(key).strip().lower().replace(" ", "").replace("_", ""): value
        for key, value in row.items()
    }
    for alias in aliases:
        key = alias.strip().lower().replace(" ", "").replace("_", "")
        if key in normalized:
            return str(normalized[key] or "").strip()
    return ""


def market_cap_column_name(row: dict, aliases: tuple[str, ...]) -> str:
    normalized_aliases = {
        alias.strip().lower().replace(" ", "").replace("_", "")
        for alias in aliases
    }
    for key in row.keys():
        normalized_key = str(key).strip().lower().replace(" ", "").replace("_", "")
        if normalized_key in normalized_aliases:
            return str(key)
    return ""


def parse_market_cap_import_value(
    value: str,
    currency: str | None,
    symbol: str,
) -> float | None:
    text = str(value or "").strip()
    if not text or text in {"-", "—"}:
        return None
    text = text.translate(str.maketrans("０１２３４５６７８９", "0123456789"))
    currency_hint = (currency or "").upper()
    if any(unit in text for unit in ("兆", "億", "万", "百万円", "千円", "円")):
        parsed = parse_japanese_money_to_yen(text)
        return parsed if is_plausible_market_cap(symbol, parsed, "JPY") else None
    cleaned = (
        text.replace(",", "")
        .replace("，", "")
        .replace("¥", "")
        .replace("$", "")
        .replace("円", "")
    )
    multiplier = 1.0
    suffix = cleaned[-1:].upper()
    if suffix in {"T", "B", "M"}:
        cleaned = cleaned[:-1]
        multiplier = {"T": 1_000_000_000_000, "B": 1_000_000_000, "M": 1_000_000}[suffix]
    try:
        numeric = float(cleaned) * multiplier
    except ValueError:
        return None
    unit_hint = str(currency or "")
    if "百万円" in unit_hint or "millionyen" in unit_hint.replace(" ", "").lower():
        numeric *= 1_000_000
    elif "億円" in unit_hint:
        numeric *= 100_000_000
    elif "千円" in unit_hint:
        numeric *= 1_000
    if not is_plausible_market_cap(symbol, numeric, currency_hint):
        return None
    return numeric


def import_market_cap_csv(csv_text: str) -> dict:
    initialize_database()
    text = (csv_text or "").lstrip("\ufeff")
    if not text.strip():
        raise ValueError("CSVが空です。")
    sample = text[:4096]
    try:
        dialect = csv.Sniffer().sniff(sample)
    except csv.Error:
        dialect = csv.excel
    reader = csv.DictReader(io.StringIO(text), dialect=dialect)
    if not reader.fieldnames:
        raise ValueError("CSVヘッダを読み取れませんでした。")

    symbol_aliases = (
        "symbol", "ticker", "code", "銘柄コード", "コード", "証券コード",
        "銘柄", "ティッカー",
    )
    market_cap_aliases = (
        "market_cap", "marketcap", "時価総額", "時価総額円",
        "時価総額(円)", "時価総額（円）", "market capitalization",
        "marketcapitalization", "時価総額百万円", "時価総額(百万円)",
        "時価総額（百万円）", "時価総額億円", "時価総額(億円)",
        "時価総額（億円）",
    )
    currency_aliases = ("currency", "通貨", "単位")
    imported = 0
    skipped = 0
    errors: list[dict] = []
    for line_number, row in enumerate(reader, start=2):
        try:
            raw_symbol = market_cap_column_value(row, symbol_aliases)
            raw_cap = market_cap_column_value(row, market_cap_aliases)
            raw_currency = market_cap_column_value(row, currency_aliases)
            cap_column = market_cap_column_name(row, market_cap_aliases)
            symbol = normalize_market_cap_import_symbol(raw_symbol)
            currency = (raw_currency or ("JPY" if symbol.endswith(".T") else "USD")).upper()
            unit_hint = raw_currency or cap_column or currency
            market_cap = parse_market_cap_import_value(raw_cap, unit_hint, symbol)
            if "円" in unit_hint or unit_hint in {"百万円", "千円"}:
                currency = "JPY"
            if market_cap is None:
                skipped += 1
                errors.append(
                    {
                        "line": line_number,
                        "symbol": raw_symbol,
                        "reason": "時価総額を数値として読めませんでした。",
                    }
                )
                continue
            save_stock_market_cap(symbol, market_cap, currency)
            imported += 1
        except Exception as exc:
            skipped += 1
            errors.append(
                {
                    "line": line_number,
                    "symbol": row.get("symbol") or row.get("コード") or "",
                    "reason": str(exc),
                }
            )
    return {
        "imported": imported,
        "skipped": skipped,
        "errors": errors[:20],
        "errorCount": len(errors),
    }


def load_cached_points(symbol: str) -> list[PricePoint]:
    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            """
            SELECT timestamp, price_date, close, high, low, volume
            FROM daily_prices
            WHERE symbol = ?
            ORDER BY timestamp
            """,
            (symbol,),
        ).fetchall()
    return [
        PricePoint(
            timestamp=int(row["timestamp"]),
            date_text=row["price_date"],
            close=float(row["close"]),
            high=float(row["high"]) if row["high"] is not None else None,
            low=float(row["low"]) if row["low"] is not None else None,
            volume=int(row["volume"]) if row["volume"] is not None else None,
        )
        for row in rows
    ]


def cached_stock_result(symbol: str) -> StockResult | None:
    row = stock_row(symbol)
    if row is None:
        return None
    points = load_cached_points(symbol)
    if not points:
        return None
    return StockResult(
        symbol=row["symbol"],
        name=row["name"],
        currency=row["currency"],
        exchange=row["exchange"],
        points=points,
        first_trade_timestamp=row["first_trade_timestamp"],
        security_type=row["security_type"] or "stock",
    )


def save_history(
    result: StockResult,
    history_complete: bool,
    long_history_complete: bool | None = None,
) -> None:
    if not result.points:
        return
    if long_history_complete is None:
        long_history_complete = False
    initialize_database()
    first_timestamp = result.first_trade_timestamp or result.points[0].timestamp
    listing_date = datetime.utcfromtimestamp(first_timestamp).strftime("%Y-%m-%d")
    last_price_date = result.points[-1].date_text
    with database_connection() as connection:
        connection.execute(
            """
            INSERT INTO stocks (
                symbol, name, currency, exchange, first_trade_timestamp,
                listing_date, last_price_date, security_type,
                history_complete, long_history_complete, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(symbol) DO UPDATE SET
                name = excluded.name,
                currency = excluded.currency,
                exchange = excluded.exchange,
                first_trade_timestamp = CASE
                    WHEN stocks.first_trade_timestamp IS NULL
                         OR excluded.first_trade_timestamp < stocks.first_trade_timestamp
                    THEN excluded.first_trade_timestamp
                    ELSE stocks.first_trade_timestamp
                END,
                listing_date = CASE
                    WHEN stocks.listing_date IS NULL
                         OR excluded.listing_date < stocks.listing_date
                    THEN excluded.listing_date
                    ELSE stocks.listing_date
                END,
                security_type = excluded.security_type,
                last_price_date = CASE
                    WHEN stocks.last_price_date IS NULL
                         OR excluded.last_price_date > stocks.last_price_date
                    THEN excluded.last_price_date
                    ELSE stocks.last_price_date
                END,
                history_complete = MAX(
                    stocks.history_complete,
                    excluded.history_complete
                ),
                long_history_complete = MAX(
                    stocks.long_history_complete,
                    excluded.long_history_complete
                ),
                updated_at = excluded.updated_at
            """,
            (
                result.symbol,
                result.name,
                result.currency,
                result.exchange,
                first_timestamp,
                listing_date,
                last_price_date,
                result.security_type,
                int(history_complete),
                int(long_history_complete),
                utc_now_text(),
            ),
        )
        connection.executemany(
            """
            INSERT INTO daily_prices (
                symbol, price_date, timestamp, close, high, low, volume
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(symbol, price_date) DO UPDATE SET
                timestamp = excluded.timestamp,
                close = excluded.close,
                high = excluded.high,
                low = excluded.low,
                volume = excluded.volume
            """,
            [
                (
                    result.symbol,
                    point.date_text,
                    point.timestamp,
                    point.close,
                    point.high,
                    point.low,
                    point.volume,
                )
                for point in result.points
            ],
        )


def analysis_summary(analysis: dict) -> dict:
    return {key: value for key, value in analysis.items() if key != "series"}


def save_analysis(symbol: str, analysis: dict) -> None:
    initialize_database()
    summary = analysis_summary(analysis)
    with database_connection() as connection:
        connection.execute(
            """
            INSERT INTO analyses (
                symbol, algorithm_version, detected, stable_date,
                calendar_days_to_stable, score_at_stable, analyzed_through,
                result_json, analyzed_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(symbol, algorithm_version) DO UPDATE SET
                detected = excluded.detected,
                stable_date = excluded.stable_date,
                calendar_days_to_stable = excluded.calendar_days_to_stable,
                score_at_stable = excluded.score_at_stable,
                analyzed_through = excluded.analyzed_through,
                result_json = excluded.result_json,
                analyzed_at = excluded.analyzed_at
            """,
            (
                symbol,
                ALGORITHM_VERSION,
                int(bool(analysis.get("detected"))),
                analysis.get("stableDate"),
                analysis.get("calendarDaysToStable"),
                analysis.get("scoreAtStable"),
                analysis.get("dataEndDate"),
                json.dumps(summary, ensure_ascii=False),
                utc_now_text(),
            ),
        )


def load_saved_analysis(symbol: str) -> dict | None:
    initialize_database()
    with database_connection() as connection:
        row = connection.execute(
            """
            SELECT result_json
            FROM analyses
            WHERE symbol = ? AND algorithm_version = ?
            """,
            (symbol, ALGORITHM_VERSION),
        ).fetchone()
    return json.loads(row["result_json"]) if row else None


def clamp(value: float, minimum: float = 0.0, maximum: float = 1.0) -> float:
    return max(minimum, min(maximum, value))


class StockDataError(RuntimeError):
    def __init__(self, category: str, message: str):
        super().__init__(message)
        self.category = category


def is_japanese_alphanumeric_symbol(symbol: str) -> bool:
    return bool(re.fullmatch(r"\d{3}[A-Z]|\d{2}[A-Z]\d|[A-Z]\d{3}", symbol))


def normalize_symbol(raw_symbol: str, market: str = "auto") -> str:
    symbol = raw_symbol.strip().upper().replace(" ", "")
    if not symbol:
        raise ValueError("銘柄コードを入力してください。")

    if "." in symbol:
        return symbol

    if market == "auto":
        if (len(symbol) == 4 and symbol.isdigit()) or is_japanese_alphanumeric_symbol(symbol):
            return f"{symbol}.T"
        return symbol

    if market not in MARKET_SUFFIXES:
        raise ValueError("市場の指定が正しくありません。")
    return f"{symbol}{MARKET_SUFFIXES[market]}"


def normalize_security_type(value: str) -> str:
    normalized = value.strip().lower()
    if normalized not in {"stock", "etf"}:
        raise ValueError("商品種別は stock または etf を指定してください。")
    return normalized


def normalize_algorithm_mode(value: str | None) -> str:
    normalized = (value or "general").strip().lower()
    if normalized not in ALGORITHM_MODES:
        raise ValueError("判定モードは general または ipo を指定してください。")
    return normalized


def request_chart(symbol: str, query: str) -> dict:
    encoded_symbol = quote(symbol, safe="")
    url = (
        "https://query1.finance.yahoo.com/v8/finance/chart/"
        f"{encoded_symbol}?{query}&includePrePost=false&events=div%2Csplits"
    )
    request = Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 Chrome/124 Safari/537.36"
            ),
            "Accept": "application/json",
        },
    )

    last_error: Exception | None = None
    for attempt in range(3):
        try:
            with batch_timing_step("Yahooチャート通信"):
                with urlopen(request, timeout=25) as response:
                    payload = json.load(response)
            break
        except HTTPError as exc:
            last_error = exc
            if exc.code == 404:
                raise StockDataError(
                    "not_found",
                    "銘柄が見つかりませんでした。上場廃止・コード変更・市場違いの可能性があります。",
                ) from exc
            if exc.code == 429:
                if attempt < 2:
                    time.sleep(1.5 * (attempt + 1))
                    continue
                raise StockDataError(
                    "rate_limit",
                    "データ取得回数の上限に達しました。少し待ってから再度お試しください。",
                ) from exc
            if 500 <= exc.code < 600 and attempt < 2:
                time.sleep(1.0 * (attempt + 1))
                continue
            raise StockDataError(
                "http_error",
                f"株価データの取得に失敗しました（HTTP {exc.code}）。",
            ) from exc
        except (URLError, TimeoutError) as exc:
            last_error = exc
            if attempt < 2:
                time.sleep(1.0 * (attempt + 1))
                continue
            raise StockDataError(
                "network",
                "通信エラーまたは時間切れです。ネットワーク状態やYahoo側の一時不調を確認してください。",
            ) from exc
    else:
        raise StockDataError(
            "unknown",
            f"株価データを取得できませんでした: {last_error}",
        )

    chart = payload.get("chart", {})
    if chart.get("error"):
        description = chart["error"].get(
            "description", "銘柄のデータを取得できませんでした。"
        )
        raise StockDataError("chart_error", f"Yahoo応答エラー: {description}")

    results = chart.get("result") or []
    if not results:
        raise StockDataError("empty_data", "この銘柄の株価データが見つかりませんでした。")
    return results[0]


def request_json_url(url: str) -> dict:
    request = Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 Chrome/124 Safari/537.36"
            ),
            "Accept": "application/json",
        },
    )
    last_error: Exception | None = None
    for attempt in range(3):
        try:
            with batch_timing_step("Yahoo補助API通信"):
                with urlopen(request, timeout=25) as response:
                    return json.load(response)
        except HTTPError as exc:
            last_error = exc
            if exc.code == 404:
                raise StockDataError("not_found", "Yahooで銘柄情報が見つかりませんでした。") from exc
            if exc.code in {401, 403}:
                raise StockDataError(
                    "auth_error",
                    f"Yahooの時価総額取得APIがアクセスを拒否しました（HTTP {exc.code}）。",
                ) from exc
            if exc.code == 429:
                if attempt < 2:
                    time.sleep(1.5 * (attempt + 1))
                    continue
                raise StockDataError("rate_limit", "Yahooの取得制限に達しました。") from exc
            if 500 <= exc.code < 600 and attempt < 2:
                time.sleep(1.0 * (attempt + 1))
                continue
            raise StockDataError("http_error", f"Yahoo取得に失敗しました（HTTP {exc.code}）。") from exc
        except (URLError, TimeoutError) as exc:
            last_error = exc
            if attempt < 2:
                time.sleep(1.0 * (attempt + 1))
                continue
            raise StockDataError("network", "通信エラーまたは時間切れです。") from exc
    raise StockDataError("unknown", f"Yahoo取得に失敗しました: {last_error}")


def request_text_url(
    url: str,
    timeout: int = 12,
    user_agent: str | None = None,
) -> str:
    request = Request(
        url,
        headers={
            "User-Agent": user_agent
            or (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 Chrome/124 Safari/537.36"
            ),
            "Accept": "text/html,application/json,text/plain,*/*",
        },
    )
    with urlopen(request, timeout=timeout) as response:
        raw = response.read()
        charset = response.headers.get_content_charset()
    encodings = [charset, "utf-8", "cp932", "shift_jis", "euc-jp"]
    for encoding in [item for item in encodings if item]:
        try:
            return raw.decode(encoding)
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace")


def strip_tags(value: str) -> str:
    value = re.sub(r"<script\b.*?</script>", " ", value, flags=re.I | re.S)
    value = re.sub(r"<style\b.*?</style>", " ", value, flags=re.I | re.S)
    value = re.sub(r"<[^>]+>", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def normalize_event_symbol(symbol: str) -> str:
    return symbol.upper().strip()


def tse_disclosure_code(symbol: str) -> str | None:
    normalized = normalize_event_symbol(symbol)
    if normalized.endswith(".T"):
        normalized = normalized[:-2]
    if re.fullmatch(r"[0-9A-Z]{4}", normalized):
        return normalized
    return None


def is_us_stock_symbol(symbol: str) -> bool:
    normalized = normalize_event_symbol(symbol)
    return bool(re.fullmatch(r"[A-Z][A-Z0-9.\-]{0,9}", normalized)) and not normalized.endswith(".T")


def disclosure_category(title: str) -> str:
    if "決算" in title:
        return "決算"
    if "上方修正" in title:
        return "上方修正"
    if "下方修正" in title:
        return "下方修正"
    if "業績" in title or "修正" in title:
        return "業績修正"
    if "配当" in title:
        return "配当"
    return "重要開示"


def dedupe_events(events: list[dict]) -> list[dict]:
    seen: set[tuple[str, str, str]] = set()
    unique: list[dict] = []
    for event in events:
        key = (
            str(event.get("eventDate", "")),
            str(event.get("title", ""))[:120],
            str(event.get("source", "")),
        )
        if not key[0] or key in seen:
            continue
        seen.add(key)
        unique.append(event)
    return sorted(unique, key=lambda item: item["eventDate"])


def parse_tdnet_disclosures(text: str, code: str, fallback_date: str) -> list[dict]:
    events: list[dict] = []
    chunks = re.split(r"</tr>|\\n|\n", text)
    if len(chunks) <= 1:
        chunks = re.split(r"\],|\},", text)
    keyword_pattern = "|".join(re.escape(item) for item in IMPORTANT_DISCLOSURE_KEYWORDS)
    for chunk in chunks:
        if code not in chunk:
            continue
        clean = strip_tags(chunk)
        if not any(keyword in clean for keyword in IMPORTANT_DISCLOSURE_KEYWORDS):
            continue
        title = ""
        title_match = re.search(
            rf"([^。\n\r<>]{{0,80}}(?:{keyword_pattern})[^。\n\r<>]{{0,120}})",
            clean,
        )
        if title_match:
            title = title_match.group(1).strip(" ,，[]'\"")
        if not title:
            title = clean[:160]
        date_match = re.search(r"(20\d{2})[/-](\d{1,2})[/-](\d{1,2})", clean)
        event_date = (
            f"{date_match.group(1)}-{int(date_match.group(2)):02d}-{int(date_match.group(3)):02d}"
            if date_match
            else fallback_date
        )
        href_match = re.search(r"href=['\"]([^'\"]+)['\"]", chunk)
        url = href_match.group(1) if href_match else ""
        if url.startswith("/"):
            url = "https://www.release.tdnet.info" + url
        elif url and not url.startswith("http"):
            url = "https://www.release.tdnet.info/inbs/" + url.lstrip("./")
        events.append(
            {
                "eventDate": event_date,
                "title": title,
                "category": disclosure_category(title),
                "source": "TDnet",
                "url": url,
            }
        )
    return dedupe_events(events)


def tdnet_candidate_urls(day: datetime) -> list[str]:
    text = day.strftime("%Y%m%d")
    return [
        f"https://www.release.tdnet.info/inbs/I_list_001_{text}.js",
        f"https://www.release.tdnet.info/inbs/I_list_001_{text}.html",
        f"https://www.release.tdnet.info/inbs/I_list_001_{text}.json",
    ]


def fetch_tdnet_events(symbol: str, lookback_days: int = IMPORTANT_EVENT_LOOKBACK_DAYS) -> list[dict]:
    from datetime import timedelta

    code = tse_disclosure_code(symbol)
    if not code:
        return []
    today = datetime.utcnow()
    events: list[dict] = []
    for offset in range(lookback_days + 1):
        day = today - timedelta(days=offset)
        if day.weekday() >= 5:
            continue
        fallback_date = day.strftime("%Y-%m-%d")
        for url in tdnet_candidate_urls(day):
            try:
                text = request_text_url(url, timeout=6)
            except Exception:
                continue
            events.extend(parse_tdnet_disclosures(text, code, fallback_date))
            if any(item["eventDate"] == fallback_date for item in events):
                break
    return dedupe_events(events)


def fetch_yahoo_earnings_events(symbol: str) -> list[dict]:
    encoded = quote(symbol, safe="")
    url = (
        "https://query2.finance.yahoo.com/v10/finance/quoteSummary/"
        f"{encoded}?modules=calendarEvents,earningsHistory"
    )
    payload = request_json_url(url)
    results = payload.get("quoteSummary", {}).get("result") or []
    if not results:
        return []
    data = results[0]
    events: list[dict] = []
    earnings_dates = (
        data.get("calendarEvents", {})
        .get("earnings", {})
        .get("earningsDate")
        or []
    )
    for item in earnings_dates:
        raw = item.get("raw") if isinstance(item, dict) else None
        if raw:
            event_date = datetime.utcfromtimestamp(int(raw)).strftime("%Y-%m-%d")
            events.append(
                {
                    "eventDate": event_date,
                    "title": "Earnings date",
                    "category": "決算予定",
                    "source": "Yahoo",
                    "url": f"https://finance.yahoo.com/quote/{quote(symbol)}/analysis",
                }
            )
    history = data.get("earningsHistory", {}).get("history") or []
    for item in history:
        quarter = item.get("quarter", {}) if isinstance(item, dict) else {}
        raw = quarter.get("raw")
        if raw:
            event_date = datetime.utcfromtimestamp(int(raw)).strftime("%Y-%m-%d")
            events.append(
                {
                    "eventDate": event_date,
                    "title": "Earnings history",
                    "category": "決算",
                    "source": "Yahoo",
                    "url": f"https://finance.yahoo.com/quote/{quote(symbol)}/analysis",
                }
            )
    return dedupe_events(events)


SEC_TICKER_CACHE: dict[str, str] = {}


def sec_user_agent() -> str:
    return "stock-event-checker/1.0 contact@example.com"


def sec_cik_for_symbol(symbol: str) -> str | None:
    normalized = normalize_event_symbol(symbol).replace(".", "-")
    if normalized in SEC_TICKER_CACHE:
        return SEC_TICKER_CACHE[normalized]
    text = request_text_url(
        "https://www.sec.gov/files/company_tickers.json",
        timeout=15,
        user_agent=sec_user_agent(),
    )
    data = json.loads(text)
    for item in data.values():
        ticker = str(item.get("ticker", "")).upper()
        if ticker == normalized:
            cik = f"{int(item['cik_str']):010d}"
            SEC_TICKER_CACHE[normalized] = cik
            return cik
    return None


def fetch_sec_filing_events(symbol: str) -> list[dict]:
    if not is_us_stock_symbol(symbol):
        return []
    cik = sec_cik_for_symbol(symbol)
    if not cik:
        return []
    text = request_text_url(
        f"https://data.sec.gov/submissions/CIK{cik}.json",
        timeout=15,
        user_agent=sec_user_agent(),
    )
    data = json.loads(text)
    recent = data.get("filings", {}).get("recent", {})
    forms = recent.get("form") or []
    filing_dates = recent.get("filingDate") or []
    primary_docs = recent.get("primaryDocument") or []
    accession_numbers = recent.get("accessionNumber") or []
    events: list[dict] = []
    for index, form in enumerate(forms):
        if form not in {"10-Q", "10-K", "8-K"}:
            continue
        filing_date = filing_dates[index] if index < len(filing_dates) else ""
        if not re.fullmatch(r"20\d{2}-\d{2}-\d{2}", filing_date):
            continue
        title = {
            "10-Q": "SEC quarterly report",
            "10-K": "SEC annual report",
            "8-K": "SEC current report",
        }.get(form, f"SEC {form}")
        accession = accession_numbers[index] if index < len(accession_numbers) else ""
        primary = primary_docs[index] if index < len(primary_docs) else ""
        clean_accession = accession.replace("-", "")
        url = (
            f"https://www.sec.gov/Archives/edgar/data/{int(cik)}/{clean_accession}/{primary}"
            if accession and primary
            else ""
        )
        events.append(
            {
                "eventDate": filing_date,
                "title": title,
                "category": "決算" if form in {"10-Q", "10-K"} else "重要開示",
                "source": "SEC",
                "url": url,
            }
        )
    return dedupe_events(events)


def save_important_events(symbol: str, events: list[dict], source: str, message: str = "") -> None:
    initialize_database()
    now = utc_now_text()
    with database_connection() as connection:
        for event in events:
            connection.execute(
                """
                INSERT OR IGNORE INTO important_events (
                    symbol, event_date, title, category, source, url, fetched_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    symbol,
                    event.get("eventDate"),
                    event.get("title", ""),
                    event.get("category", ""),
                    event.get("source", source),
                    event.get("url", ""),
                    now,
                ),
            )
        connection.execute(
            """
            INSERT INTO important_event_fetch_log (
                symbol, source, fetched_at, status, message
            ) VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(symbol, source) DO UPDATE SET
                fetched_at = excluded.fetched_at,
                status = excluded.status,
                message = excluded.message
            """,
            (symbol, source, now, "ok", message),
        )


def save_important_event_error(symbol: str, source: str, message: str) -> None:
    initialize_database()
    with database_connection() as connection:
        connection.execute(
            """
            INSERT INTO important_event_fetch_log (
                symbol, source, fetched_at, status, message
            ) VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(symbol, source) DO UPDATE SET
                fetched_at = excluded.fetched_at,
                status = excluded.status,
                message = excluded.message
            """,
            (symbol, source, utc_now_text(), "error", message[:300]),
        )


def should_refresh_event_source(symbol: str, source: str) -> bool:
    initialize_database()
    with database_connection() as connection:
        row = connection.execute(
            """
            SELECT fetched_at FROM important_event_fetch_log
            WHERE symbol = ? AND source = ?
            """,
            (symbol, source),
        ).fetchone()
    if row is None:
        return True
    try:
        fetched_at = datetime.strptime(row["fetched_at"], "%Y-%m-%d %H:%M:%S")
    except ValueError:
        return True
    return (datetime.utcnow() - fetched_at).total_seconds() > IMPORTANT_EVENT_REFRESH_HOURS * 3600


def ensure_important_events_cache(symbol: str) -> None:
    sources: list[tuple[str, object]] = []
    if tse_disclosure_code(symbol):
        sources.append(("TDnet", fetch_tdnet_events))
    if is_us_stock_symbol(symbol):
        sources.append(("SEC", fetch_sec_filing_events))
    sources.append(("Yahoo", fetch_yahoo_earnings_events))
    for source, fetcher in sources:
        if not should_refresh_event_source(symbol, source):
            continue
        try:
            events = fetcher(symbol)  # type: ignore[operator]
            save_important_events(symbol, events, source, f"{len(events)} events")
        except Exception as exc:
            save_important_event_error(symbol, source, str(exc))


def load_important_events(symbol: str, start_date: str | None = None, end_date: str | None = None) -> list[dict]:
    initialize_database()
    conditions = ["symbol = ?"]
    params: list[object] = [symbol]
    if start_date:
        conditions.append("event_date >= ?")
        params.append(start_date)
    if end_date:
        conditions.append("event_date <= ?")
        params.append(end_date)
    with database_connection() as connection:
        rows = connection.execute(
            f"""
            SELECT event_date, title, category, source, url, fetched_at
            FROM important_events
            WHERE {' AND '.join(conditions)}
            ORDER BY event_date, source, title
            """,
            params,
        ).fetchall()
    return [
        {
            "eventDate": row["event_date"],
            "title": row["title"],
            "category": row["category"],
            "source": row["source"],
            "url": row["url"],
            "fetchedAt": row["fetched_at"],
        }
        for row in rows
    ]


def known_important_events(symbol: str, start_date: str | None = None, end_date: str | None = None) -> list[dict]:
    events = []
    for event_date, title, category in KNOWN_IMPORTANT_EVENTS.get(symbol, []):
        if start_date and event_date < start_date:
            continue
        if end_date and event_date > end_date:
            continue
        events.append(
            {
                "eventDate": event_date,
                "title": title,
                "category": category,
                "source": "手動登録",
                "url": "",
                "fetchedAt": "",
            }
        )
    return events


def important_events_for_display(symbol: str, start_date: str | None = None, end_date: str | None = None) -> list[dict]:
    return dedupe_events(
        load_important_events(symbol, start_date, end_date)
        + known_important_events(symbol, start_date, end_date)
    )


def event_fetch_logs(symbol: str) -> list[dict]:
    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            """
            SELECT source, fetched_at, status, message
            FROM important_event_fetch_log
            WHERE symbol = ?
            ORDER BY source
            """,
            (symbol,),
        ).fetchall()
    return [
        {
            "source": row["source"],
            "fetchedAt": row["fetched_at"],
            "status": row["status"],
            "message": row["message"],
        }
        for row in rows
    ]


def fetch_important_events_payload(
    symbol: str,
    display_start: str | None = None,
    display_end: str | None = None,
) -> dict:
    ensure_important_events_cache(symbol)
    cached = cached_stock_result(symbol)
    points = cached.points if cached else []
    display_points = [
        point
        for point in points
        if (not display_start or point.date_text >= display_start)
        and (not display_end or point.date_text <= display_end)
    ] or points
    return {
        "symbol": symbol,
        "importantEvents": annotate_important_events(
            important_events_for_display(symbol, display_start, display_end),
            display_points,
        ),
        "allImportantEvents": annotate_important_events(
            important_events_for_display(symbol),
            points,
        ),
        "logs": event_fetch_logs(symbol),
    }


def annotate_important_events(events: list[dict], points: list[PricePoint]) -> list[dict]:
    if not events or not points:
        return events
    index_by_date = {point.date_text: index for index, point in enumerate(points)}
    dates = [point.date_text for point in points]
    annotated: list[dict] = []
    for event in events:
        index = index_by_date.get(event["eventDate"])
        if index is None:
            later_indexes = [
                offset for offset, date_text in enumerate(dates)
                if date_text >= event["eventDate"]
            ]
            if not later_indexes:
                continue
            index = later_indexes[0]
        previous_index = max(0, index - 1)
        after_index = min(len(points) - 1, index + 3)
        before_close = points[previous_index].close
        after_close = points[after_index].close
        impact = (after_close / before_close - 1) * 100 if before_close else None
        previous_volumes = [
            point.volume for point in points[max(0, index - 20):index]
            if point.volume is not None and point.volume > 0
        ]
        volume_ratio = None
        if previous_volumes and points[index].volume:
            volume_ratio = points[index].volume / mean(previous_volumes)
        item = dict(event)
        item["chartDate"] = points[index].date_text
        item["impactPercent"] = round(impact, 2) if impact is not None else None
        item["volumeRatio"] = round(volume_ratio, 2) if volume_ratio is not None else None
        item["material"] = bool(
            (impact is not None and abs(impact) >= IMPORTANT_EVENT_MOVE_THRESHOLD)
            or (
                volume_ratio is not None
                and volume_ratio >= IMPORTANT_EVENT_VOLUME_THRESHOLD
            )
        )
        annotated.append(item)
    return annotated


def fetch_market_caps(symbols: list[str]) -> dict[str, int | None]:
    market_caps: dict[str, int | None] = {symbol: None for symbol in symbols}
    unique_symbols = list(dict.fromkeys(symbols))
    for offset in range(0, len(unique_symbols), 60):
        chunk = unique_symbols[offset : offset + 60]
        encoded = quote(",".join(chunk), safe=",")
        url = f"https://query1.finance.yahoo.com/v7/finance/quote?symbols={encoded}"
        payload = request_json_url(url)
        results = payload.get("quoteResponse", {}).get("result", [])
        for item in results:
            symbol = item.get("symbol")
            if symbol in market_caps:
                value = item.get("marketCap")
                currency = item.get("currency") or ""
                market_caps[symbol] = (
                    int(value)
                    if isinstance(value, (int, float))
                    and is_plausible_market_cap(symbol, value, currency)
                    else None
                )
                if market_caps[symbol] is not None:
                    save_stock_market_cap(
                        symbol,
                        market_caps[symbol],
                        currency,
                    )
    missing_symbols = [symbol for symbol, value in market_caps.items() if value is None]
    for symbol in missing_symbols:
        cached_value, _cached_currency = cached_stock_market_cap(symbol)
        if cached_value:
            market_caps[symbol] = int(cached_value)
            continue
        cached_result = cached_stock_result(symbol)
        current_price = cached_result.points[-1].close if cached_result and cached_result.points else 0.0
        value, currency = quote_market_cap_and_currency(
            symbol,
            current_price,
            "JPY" if symbol.endswith(".T") else "",
        )
        if value:
            market_caps[symbol] = int(value)
            save_stock_market_cap(symbol, value, currency)
    return market_caps


FX_JPY_FALLBACKS = {
    "JPY": 1.0,
    "USD": 160.0,
    "EUR": 172.0,
    "GBP": 202.0,
    "HKD": 20.5,
    "CNY": 22.0,
    "TWD": 5.0,
}
FX_JPY_CACHE: dict[str, tuple[float, float]] = {}
QUOTE_SUMMARY_CACHE: dict[str, tuple[float, dict]] = {}
QUOTE_DETAIL_CACHE: dict[str, tuple[float, dict]] = {}
FX_CACHE_SECONDS = 6 * 60 * 60
QUOTE_SUMMARY_CACHE_SECONDS = 30 * 60


def currency_to_jpy_rate(currency: str | None) -> float:
    normalized = (currency or "JPY").strip().upper()
    if normalized in {"", "JPY"}:
        return 1.0
    now = time.time()
    cached = FX_JPY_CACHE.get(normalized)
    if cached and now - cached[0] < FX_CACHE_SECONDS:
        return cached[1]
    fallback = FX_JPY_FALLBACKS.get(normalized, 1.0)
    pair = f"{normalized}JPY=X"
    try:
        result = request_chart(pair, "range=5d&interval=1d")
        points = parse_chart_result(result, pair).points
        rate = points[-1].close if points else fallback
        if not math.isfinite(rate) or rate <= 0:
            rate = fallback
    except Exception:
        rate = fallback
    FX_JPY_CACHE[normalized] = (now, float(rate))
    return float(rate)


def to_jpy_amount(value: float | int | None, currency: str | None) -> int | None:
    if value is None:
        return None
    try:
        numeric = float(value)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(numeric):
        return None
    return int(round(numeric * currency_to_jpy_rate(currency)))


def fetch_quote_summary(symbol: str) -> dict:
    normalized = symbol.strip()
    now = time.time()
    cached = QUOTE_SUMMARY_CACHE.get(normalized)
    if cached and now - cached[0] < QUOTE_SUMMARY_CACHE_SECONDS:
        return dict(cached[1])
    encoded = quote(normalized, safe="")
    results = []
    last_error: Exception | None = None
    for url in [
        f"https://query1.finance.yahoo.com/v7/finance/quote?symbols={encoded}",
        f"https://query2.finance.yahoo.com/v7/finance/quote?symbols={encoded}",
        f"https://query1.finance.yahoo.com/v6/finance/quote?symbols={encoded}",
        f"https://query2.finance.yahoo.com/v6/finance/quote?symbols={encoded}",
    ]:
        try:
            payload = request_json_url(url)
            results = payload.get("quoteResponse", {}).get("result", [])
            if results:
                break
        except Exception as exc:
            last_error = exc
            continue
    if not results and last_error:
        raise last_error
    summary = dict(results[0]) if results else {}
    QUOTE_SUMMARY_CACHE[normalized] = (now, summary)
    return dict(summary)


def yahoo_raw_value(value: object) -> float | None:
    if isinstance(value, dict):
        value = value.get("raw", value.get("fmt"))
    if isinstance(value, (int, float)):
        numeric = float(value)
    else:
        try:
            numeric = float(str(value).replace(",", ""))
        except (TypeError, ValueError):
            return None
    return numeric if math.isfinite(numeric) else None


def parse_japanese_money_to_yen(value: str) -> float | None:
    text = re.sub(r"\s+", "", value)
    text = text.replace(",", "").replace("，", "")
    if not text or text in {"-", "—"}:
        return None
    total = 0.0
    matched = False
    for number, unit in re.findall(r"([0-9]+(?:\.[0-9]+)?)(兆|億|万)?", text):
        if not number:
            continue
        amount = float(number)
        matched = True
        if unit == "兆":
            total += amount * 1_000_000_000_000
        elif unit == "億":
            total += amount * 100_000_000
        elif unit == "万":
            total += amount * 10_000
        else:
            total += amount
    if not matched:
        return None
    if "百万円" in text:
        return total * 1_000_000
    if "千円" in text:
        return total * 1_000
    return total


def is_plausible_market_cap(
    symbol: str,
    market_cap: float | int | None,
    currency: str | None = "",
) -> bool:
    if market_cap is None:
        return False
    try:
        numeric = float(market_cap)
    except (TypeError, ValueError):
        return False
    if not math.isfinite(numeric) or numeric <= 0:
        return False
    normalized_currency = (currency or "").upper()
    # 誤スクレイピングで「8円」のような値を拾う事故を防ぐ。
    # 上場企業の時価総額としては極端に小さすぎる値は利用しない。
    if symbol.upper().endswith(".T") or normalized_currency == "JPY":
        return numeric >= 100_000_000
    return numeric >= 1_000_000


def fetch_quote_detail_summary(symbol: str) -> dict:
    normalized = symbol.strip()
    now = time.time()
    cached = QUOTE_DETAIL_CACHE.get(normalized)
    if cached and now - cached[0] < QUOTE_SUMMARY_CACHE_SECONDS:
        return dict(cached[1])
    encoded = quote(normalized, safe="")
    url = (
        "https://query2.finance.yahoo.com/v10/finance/quoteSummary/"
        f"{encoded}?modules=price,summaryDetail,defaultKeyStatistics"
    )
    payload = request_json_url(url)
    results = payload.get("quoteSummary", {}).get("result") or []
    summary = dict(results[0]) if results else {}
    QUOTE_DETAIL_CACHE[normalized] = (now, summary)
    return dict(summary)


def fetch_market_cap_from_yahoo_page(symbol: str) -> tuple[float | None, str]:
    try:
        encoded = quote(symbol, safe="")
        text = request_text_url(
            f"https://finance.yahoo.com/quote/{encoded}",
            timeout=10,
        )
    except Exception:
        return None, ""
    patterns = [
        r'"marketCap"\s*:\s*\{\s*"raw"\s*:\s*([0-9.eE+-]+)',
        r'"marketCap"\s*:\s*([0-9.eE+-]+)',
    ]
    for pattern in patterns:
        match = re.search(pattern, text)
        if match:
            value = yahoo_raw_value(match.group(1))
            if value and value > 0:
                currency_match = re.search(r'"currency"\s*:\s*"([A-Z]{3})"', text)
                return value, currency_match.group(1) if currency_match else ""
    return None, ""


def japanese_stock_code(symbol: str) -> str | None:
    normalized = symbol.upper().strip()
    match = re.fullmatch(r"(\d{4})\.T", normalized)
    return match.group(1) if match else None


def fetch_market_cap_from_yahoo_japan(symbol: str) -> tuple[float | None, str]:
    code = japanese_stock_code(symbol)
    if not code:
        return None, ""
    candidates = [
        f"https://finance.yahoo.co.jp/quote/{code}.T",
        f"https://finance.yahoo.co.jp/quote/{code}.T/profile",
    ]
    for url in candidates:
        try:
            text = request_text_url(url, timeout=10)
        except Exception:
            continue
        patterns = [
            r"時価総額[^0-9０-９]{0,80}([0-9０-９,，.]+(?:兆|億|万)?(?:[0-9０-９,，.]+(?:億|万))?円?)",
            r'"marketCapitalization"[^0-9]{0,40}([0-9.eE+-]+)',
            r'"marketCap"[^0-9]{0,40}([0-9.eE+-]+)',
        ]
        for pattern in patterns:
            match = re.search(pattern, text)
            if not match:
                continue
            raw = match.group(1).translate(str.maketrans("０１２３４５６７８９", "0123456789"))
            value = yahoo_raw_value(raw)
            if not value:
                value = parse_japanese_money_to_yen(raw)
            if value and value > 0:
                save_stock_market_cap(symbol, value, "JPY")
                return value, "JPY"
    return None, ""


def fetch_market_cap_from_kabutan(symbol: str) -> tuple[float | None, str]:
    code = japanese_stock_code(symbol)
    if not code:
        return None, ""
    try:
        text = request_text_url(
            f"https://kabutan.jp/stock/?code={code}",
            timeout=10,
        )
    except Exception:
        return None, ""
    for pattern in [
        r"時価総額</th>\s*<td[^>]*>\s*([^<]+)",
        r"時価総額[^0-9０-９]{0,120}([0-9０-９,，.]+(?:兆|億|万)?(?:[0-9０-９,，.]+(?:億|万))?円?)",
    ]:
        match = re.search(pattern, text)
        if not match:
            continue
        raw = re.sub(r"<[^>]+>", "", match.group(1))
        raw = raw.translate(str.maketrans("０１２３４５６７８９", "0123456789"))
        value = parse_japanese_money_to_yen(raw)
        if value and value > 0:
            save_stock_market_cap(symbol, value, "JPY")
            return value, "JPY"
    return None, ""


def quote_market_cap_and_currency(
    symbol: str,
    current_price: float,
    currency: str | None,
) -> tuple[float | None, str]:
    quote_currency = currency or ""
    cached_market_cap, cached_currency = cached_stock_market_cap(symbol)
    if cached_market_cap and cached_market_cap > 0:
        return cached_market_cap, cached_currency or quote_currency
    try:
        summary = fetch_quote_summary(symbol)
    except Exception:
        summary = {}
    quote_currency = summary.get("currency") or quote_currency
    market_cap = yahoo_raw_value(summary.get("marketCap"))
    if is_plausible_market_cap(symbol, market_cap, quote_currency):
        save_stock_market_cap(symbol, market_cap, quote_currency)
        return market_cap, quote_currency

    try:
        detail = fetch_quote_detail_summary(symbol)
    except Exception:
        detail = {}
    price_data = detail.get("price") or {}
    stats_data = detail.get("defaultKeyStatistics") or {}
    summary_detail = detail.get("summaryDetail") or {}
    quote_currency = (
        price_data.get("currency")
        or summary_detail.get("currency")
        or quote_currency
    )
    market_cap = (
        yahoo_raw_value(price_data.get("marketCap"))
        or yahoo_raw_value(summary_detail.get("marketCap"))
    )
    if is_plausible_market_cap(symbol, market_cap, quote_currency):
        save_stock_market_cap(symbol, market_cap, quote_currency)
        return market_cap, quote_currency

    shares = (
        yahoo_raw_value(stats_data.get("sharesOutstanding"))
        or yahoo_raw_value(stats_data.get("impliedSharesOutstanding"))
        or yahoo_raw_value(price_data.get("sharesOutstanding"))
    )
    if shares and shares > 0 and current_price > 0:
        market_cap = shares * current_price
        if is_plausible_market_cap(symbol, market_cap, quote_currency):
            save_stock_market_cap(symbol, market_cap, quote_currency)
            return market_cap, quote_currency
    page_market_cap, page_currency = fetch_market_cap_from_yahoo_page(symbol)
    if is_plausible_market_cap(symbol, page_market_cap, page_currency or quote_currency):
        quote_currency = page_currency or quote_currency
        save_stock_market_cap(symbol, page_market_cap, quote_currency)
        return page_market_cap, quote_currency
    yahoo_jp_market_cap, yahoo_jp_currency = fetch_market_cap_from_yahoo_japan(symbol)
    if is_plausible_market_cap(symbol, yahoo_jp_market_cap, yahoo_jp_currency or "JPY"):
        return yahoo_jp_market_cap, yahoo_jp_currency or "JPY"
    kabutan_market_cap, kabutan_currency = fetch_market_cap_from_kabutan(symbol)
    if is_plausible_market_cap(symbol, kabutan_market_cap, kabutan_currency or "JPY"):
        return kabutan_market_cap, kabutan_currency or "JPY"
    return None, quote_currency


def estimated_market_cap_at_price_jpy(
    symbol: str,
    price: float | int | None,
    current_price: float | int | None,
    currency: str | None,
) -> tuple[int | None, int | None, str]:
    if price is None or current_price is None:
        return None, None, ""
    try:
        price_value = float(price)
        current_value = float(current_price)
    except (TypeError, ValueError):
        return None, None, ""
    if price_value <= 0 or current_value <= 0:
        return None, None, ""
    market_cap, quote_currency = quote_market_cap_and_currency(
        symbol,
        current_value,
        currency,
    )
    if market_cap is None or market_cap <= 0:
        return None, None, ""
    current_market_cap_jpy = to_jpy_amount(market_cap, quote_currency)
    if current_market_cap_jpy is None:
        return None, None, ""
    estimated = int(round(current_market_cap_jpy * (price_value / current_value)))
    return estimated, current_market_cap_jpy, quote_currency or ""


def parse_chart_result(result: dict, requested_symbol: str) -> StockResult:
    meta = result.get("meta", {})
    timestamps = result.get("timestamp") or []
    indicators = result.get("indicators") or {}
    quote_data = (indicators.get("quote") or [{}])[0]
    adjusted_data = (indicators.get("adjclose") or [{}])[0]

    raw_closes = quote_data.get("close") or []
    adjusted_closes = adjusted_data.get("adjclose") or []
    highs = quote_data.get("high") or []
    lows = quote_data.get("low") or []
    volumes = quote_data.get("volume") or []

    points: list[PricePoint] = []
    for index, timestamp in enumerate(timestamps):
        raw_close = raw_closes[index] if index < len(raw_closes) else None
        adjusted_close = (
            adjusted_closes[index] if index < len(adjusted_closes) else raw_close
        )
        if adjusted_close is None or not math.isfinite(adjusted_close):
            continue

        factor = 1.0
        if raw_close and math.isfinite(raw_close):
            factor = adjusted_close / raw_close

        high = highs[index] if index < len(highs) else None
        low = lows[index] if index < len(lows) else None
        if high is not None and math.isfinite(high):
            high = float(high) * factor
        else:
            high = None
        if low is not None and math.isfinite(low):
            low = float(low) * factor
        else:
            low = None
        volume = volumes[index] if index < len(volumes) else None
        if volume is not None and math.isfinite(volume):
            volume = int(volume)
        else:
            volume = None

        points.append(
            PricePoint(
                timestamp=int(timestamp),
                date_text=datetime.utcfromtimestamp(timestamp).strftime("%Y-%m-%d"),
                close=float(adjusted_close),
                high=high,
                low=low,
                volume=volume,
            )
        )

    if not points:
        raise ValueError("選択期間内に表示できる株価データがありません。")

    first_trade = meta.get("firstTradeDate")
    return StockResult(
        symbol=meta.get("symbol", requested_symbol),
        name=meta.get("longName") or meta.get("shortName") or requested_symbol,
        currency=meta.get("currency", ""),
        exchange=meta.get("fullExchangeName") or meta.get("exchangeName", ""),
        points=points,
        first_trade_timestamp=int(first_trade) if first_trade else points[0].timestamp,
    )


def fetch_stock_data(symbol: str, period: str) -> StockResult:
    if period not in PERIODS:
        raise ValueError("表示期間の指定が正しくありません。")
    range_value, interval = PERIODS[period]
    result = request_chart(symbol, f"range={range_value}&interval={interval}")
    return parse_chart_result(result, symbol)


def fetch_listing_history(
    symbol: str, first_trade_timestamp: int | None = None
) -> StockResult:
    if not first_trade_timestamp:
        metadata = fetch_stock_data(symbol, "1mo")
        first_trade_timestamp = metadata.first_trade_timestamp

    if not first_trade_timestamp:
        raise ValueError("上場後分析の開始日を取得できませんでした。")

    now = int(time.time()) + 86400
    analysis_end = min(
        now,
        first_trade_timestamp + int(ANALYSIS_MAX_YEARS * 366 * 86400),
    )
    query = (
        f"period1={max(0, first_trade_timestamp - 86400)}"
        f"&period2={analysis_end}&interval=1d"
    )
    result = request_chart(symbol, query)
    return parse_chart_result(result, symbol)


def fetch_full_daily_history(
    symbol: str, first_trade_timestamp: int | None = None
) -> StockResult:
    if not first_trade_timestamp:
        metadata = fetch_stock_data(symbol, "1mo")
        first_trade_timestamp = metadata.first_trade_timestamp

    if not first_trade_timestamp:
        raise ValueError("長期分析の開始日を取得できませんでした。")

    query = (
        f"period1={max(0, first_trade_timestamp - 86400)}"
        f"&period2={int(time.time()) + 86400}&interval=1d"
    )
    result = request_chart(symbol, query)
    return parse_chart_result(result, symbol)


def fetch_history_range(
    symbol: str, period1: int, period2: int
) -> StockResult:
    if period2 <= period1:
        raise ValueError("追加取得する日付範囲がありません。")
    query = (
        f"period1={max(0, period1)}"
        f"&period2={period2}&interval=1d"
    )
    result = request_chart(symbol, query)
    return parse_chart_result(result, symbol)


def history_is_complete(
    first_trade_timestamp: int, last_timestamp: int
) -> bool:
    horizon = analysis_horizon_timestamp(first_trade_timestamp)
    return last_timestamp >= horizon - 10 * 86400


def long_history_is_complete(last_timestamp: int) -> bool:
    return last_timestamp >= int(time.time()) - 10 * 86400


def cached_history_is_recent(last_timestamp: int) -> bool:
    """直近データが十分新しければ、その銘柄の通信更新を省略する。"""
    return last_timestamp >= int(time.time()) - 3 * 86400


def fetch_incremental_daily_history(
    cached: StockResult,
    target_timestamp: int,
    security_type: str,
) -> tuple[StockResult | None, bool]:
    """保存済み最終日付の少し前から差分だけ取得し、重複日はDBで上書きする。"""
    if not cached.points:
        return None, False
    first_timestamp = cached.first_trade_timestamp or cached.points[0].timestamp
    last_timestamp = cached.points[-1].timestamp
    if target_timestamp <= last_timestamp + 86400:
        return None, False
    period1 = max(
        first_timestamp - 86400,
        last_timestamp - INCREMENTAL_OVERLAP_DAYS * 86400,
    )
    period2 = target_timestamp
    if period2 <= period1 + 86400:
        return None, False
    with batch_timing_step("差分日足取得"):
        fetched = fetch_history_range(cached.symbol, period1, period2)
    fetched = replace(fetched, security_type=security_type)
    fetched_last = fetched.points[-1].timestamp if fetched.points else last_timestamp
    save_history(
        fetched,
        history_is_complete(first_timestamp, fetched_last),
        long_history_complete=long_history_is_complete(fetched_last),
    )
    return fetched, fetched_last > last_timestamp


def nearest_price_point_on_or_after(
    points: list[PricePoint],
    date_text: str | None,
) -> PricePoint | None:
    if not date_text:
        return None
    for point in points:
        if point.date_text >= date_text:
            return point
    return None


def benchmark_history() -> StockResult | None:
    cached = cached_stock_result(BENCHMARK_SYMBOL)
    if cached is not None and cached.points:
        if not cached_history_is_recent(cached.points[-1].timestamp):
            try:
                fetch_incremental_daily_history(
                    cached,
                    int(time.time()) + 86400,
                    "etf",
                )
                return cached_stock_result(BENCHMARK_SYMBOL) or cached
            except Exception:
                return cached
        return cached
    try:
        metadata = fetch_stock_data(BENCHMARK_SYMBOL, "1mo")
        fetched = fetch_full_daily_history(
            BENCHMARK_SYMBOL,
            metadata.first_trade_timestamp,
        )
        fetched = replace(fetched, security_type="etf")
        first_timestamp = (
            fetched.first_trade_timestamp or fetched.points[0].timestamp
        )
        save_history(
            fetched,
            history_is_complete(first_timestamp, fetched.points[-1].timestamp),
            long_history_is_complete(fetched.points[-1].timestamp),
        )
        return cached_stock_result(BENCHMARK_SYMBOL) or fetched
    except Exception:
        return None


def add_benchmark_performance_to_evaluations(
    evaluations: list[dict],
    benchmark_points: list[PricePoint] | None,
) -> None:
    points = clean_price_points(benchmark_points or [])
    if not evaluations or not points:
        return
    current_point = points[-1]
    current_price = current_point.close
    for evaluation in evaluations:
        buy_point = nearest_price_point_on_or_after(
            points,
            evaluation.get("date"),
        )
        if buy_point is None or not buy_point.close:
            continue
        return_percent = (current_price / buy_point.close - 1) * 100
        rank_candidates = [
            ("immediateBuyRank", evaluation.get("holdingReturnPercent")),
            ("drawdownBuyRank", evaluation.get("drawdownHoldingReturnPercent")),
            ("delayedBuyRank", evaluation.get("delayedHoldingReturnPercent")),
            ("benchmarkBuyRank", round(return_percent, 2)),
        ]
        ranked = [
            (key, float(value))
            for key, value in rank_candidates
            if value is not None
        ]
        ranked.sort(key=lambda item: item[1], reverse=True)
        rank_values = {
            "immediateBuyRank": None,
            "drawdownBuyRank": None,
            "delayedBuyRank": None,
            "benchmarkBuyRank": None,
        }
        for rank, (key, _value) in enumerate(ranked, start=1):
            rank_values[key] = rank
        evaluation.update(
            {
                "benchmarkSymbol": BENCHMARK_SYMBOL,
                "benchmarkLabel": BENCHMARK_LABEL,
                "benchmarkBuyDate": buy_point.date_text,
                "benchmarkBuyPrice": round(buy_point.close, 4),
                "benchmarkCurrentDate": current_point.date_text,
                "benchmarkCurrentPrice": round(current_price, 4),
                "benchmarkHoldingReturnPercent": round(return_percent, 2),
                **rank_values,
            }
        )


def volume_data_is_sufficient(points: list[PricePoint]) -> bool:
    if not points:
        return False
    populated = sum(
        point.volume is not None and point.volume > 0 for point in points
    )
    return populated >= len(points) * 0.80


def ensure_symbol_cache(
    symbol: str,
    metadata: StockResult | None = None,
    update_missing: bool = True,
    security_type: str = "stock",
    history_scope: str = "ipo",
    prefer_saved_analysis: bool = False,
) -> tuple[StockResult, dict, bool]:
    """銘柄の日足と分析結果を保存し、必要な場合だけ差分取得する。"""
    initialize_database()
    if history_scope not in {"ipo", "long"}:
        raise ValueError("履歴取得モードは ipo または long を指定してください。")
    security_type = normalize_security_type(security_type)
    cached_row = stock_row(symbol)
    cached = cached_stock_result(symbol)
    if cached is not None:
        security_type = cached.security_type
    elif metadata is not None:
        metadata = replace(metadata, security_type=security_type)
    saved_analysis = load_saved_analysis(symbol)
    changed = False

    # 旧DBには出来高列がないため、価格ブレイク版へ移行するときは一度だけ
    # 上場後データを再取得し、出来高を補完する。
    if (
        cached is not None
        and update_missing
        and not volume_data_is_sufficient(cached.points)
    ):
        fetched = fetch_listing_history(
            symbol, cached.first_trade_timestamp
        )
        first_timestamp = (
            fetched.first_trade_timestamp or fetched.points[0].timestamp
        )
        save_history(
            fetched,
            history_is_complete(
                first_timestamp, fetched.points[-1].timestamp
            ),
            long_history_complete=False,
        )
        cached_row = stock_row(symbol)
        cached = cached_stock_result(symbol)
        changed = True

    # 現行アルゴリズムで底打ち候補が確定済みなら、その過去データは通常更新しない。
    long_cache_complete = bool(
        cached_row and cached_row["long_history_complete"]
    )
    if (
        cached is not None
        and saved_analysis
        and saved_analysis.get("detected")
        and (history_scope != "long" or long_cache_complete)
    ):
        latest_date = cached.points[-1].date_text if cached.points else None
        if (
            prefer_saved_analysis
            and saved_analysis.get("dataEndDate") == latest_date
        ):
            with batch_timing_step("保存済み分析結果を利用・再計算省略"):
                return cached, saved_analysis, False
        with batch_timing_step("保存済み日足から底練り再計算"):
            full_analysis = analyze_stability(
                cached.points, cached.security_type
            )
        return cached, full_analysis, False

    if cached is None:
        if metadata is None:
            metadata = replace(
                fetch_stock_data(symbol, "1mo"),
                security_type=security_type,
            )
        if history_scope == "long":
            fetched = fetch_full_daily_history(
                symbol, metadata.first_trade_timestamp
            )
        else:
            fetched = fetch_listing_history(
                symbol, metadata.first_trade_timestamp
            )
        fetched = replace(fetched, security_type=security_type)
        first_timestamp = fetched.first_trade_timestamp or fetched.points[0].timestamp
        complete = history_is_complete(first_timestamp, fetched.points[-1].timestamp)
        long_complete = (
            long_history_is_complete(fetched.points[-1].timestamp)
            if history_scope == "long"
            else False
        )
        save_history(fetched, complete, long_complete)
        cached_row = stock_row(symbol)
        cached = cached_stock_result(symbol)
        changed = True
    elif update_missing:
        first_timestamp = (
            cached.first_trade_timestamp or cached.points[0].timestamp
        )
        last_timestamp = cached.points[-1].timestamp
        inferred_full_span = (
            cached.points[0].timestamp <= first_timestamp + 10 * 86400
            and cached_history_is_recent(last_timestamp)
        )
        if history_scope == "long":
            complete = bool(
                (
                    cached_row
                    and cached_row["long_history_complete"]
                    and long_history_is_complete(last_timestamp)
                )
                or inferred_full_span
            )
            target_timestamp = int(time.time()) + 86400
        else:
            complete = history_is_complete(first_timestamp, last_timestamp)
            target_timestamp = analysis_horizon_timestamp(first_timestamp)
        if complete:
            with batch_timing_step("保存済み日足を利用・通信省略"):
                pass
        else:
            _fetched, updated = fetch_incremental_daily_history(
                cached,
                target_timestamp,
                security_type,
            )
            if updated:
                cached_row = stock_row(symbol)
                cached = cached_stock_result(symbol)
                changed = True

    if cached is None:
        raise ValueError("保存用の株価履歴を作成できませんでした。")

    latest_date = cached.points[-1].date_text
    analysis_needs_refresh = (
        changed
        or saved_analysis is None
        or saved_analysis.get("dataEndDate") != latest_date
    )
    if prefer_saved_analysis and not analysis_needs_refresh:
        with batch_timing_step("保存済み分析結果を利用・再計算省略"):
            return cached, saved_analysis, changed
    with batch_timing_step("保存済み日足から底練り再計算"):
        full_analysis = analyze_stability(
            cached.points, cached.security_type
        )
    if analysis_needs_refresh:
        save_analysis(symbol, full_analysis)
    return cached, full_analysis, changed


def reanalyze_cached_symbols(only_missing: bool) -> dict:
    initialize_database()
    with database_connection() as connection:
        if only_missing:
            rows = connection.execute(
                """
                SELECT s.symbol, s.security_type
                FROM stocks s
                LEFT JOIN analyses a
                  ON a.symbol = s.symbol
                 AND a.algorithm_version = ?
                WHERE a.symbol IS NULL
                ORDER BY s.symbol
                """,
                (ALGORITHM_VERSION,),
            ).fetchall()
        else:
            rows = connection.execute(
                "SELECT symbol, security_type FROM stocks ORDER BY symbol"
            ).fetchall()

    completed = 0
    errors: list[dict] = []
    for row in rows:
        symbol = row["symbol"]
        try:
            points = load_cached_points(symbol)
            if not points:
                raise ValueError("保存済み日足がありません。")
            save_analysis(
                symbol,
                analyze_stability(points, row["security_type"]),
            )
            completed += 1
        except Exception as exc:
            errors.append({"symbol": symbol, "error": str(exc)})
    return {
        "targetCount": len(rows),
        "completedCount": completed,
        "errors": errors,
    }


def update_all_cached_symbols() -> dict:
    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            "SELECT symbol FROM stocks ORDER BY symbol"
        ).fetchall()

    updated = 0
    skipped = 0
    errors: list[dict] = []
    for row in rows:
        symbol = row["symbol"]
        try:
            _history, _analysis, changed = ensure_symbol_cache(
                symbol, update_missing=True
            )
            if changed:
                updated += 1
            else:
                skipped += 1
        except Exception as exc:
            errors.append({"symbol": symbol, "error": str(exc)})
    return {
        "targetCount": len(rows),
        "updatedCount": updated,
        "skippedCount": skipped,
        "errors": errors,
    }


def cache_status() -> dict:
    initialize_database()
    with database_connection() as connection:
        stock_count = connection.execute(
            "SELECT COUNT(*) FROM stocks"
        ).fetchone()[0]
        price_count = connection.execute(
            "SELECT COUNT(*) FROM daily_prices"
        ).fetchone()[0]
        current_analysis_count = connection.execute(
            """
            SELECT COUNT(*) FROM analyses
            WHERE algorithm_version = ?
            """,
            (ALGORITHM_VERSION,),
        ).fetchone()[0]
        detected_count = connection.execute(
            """
            SELECT COUNT(*) FROM analyses
            WHERE algorithm_version = ? AND detected = 1
            """,
            (ALGORITHM_VERSION,),
        ).fetchone()[0]
        last_updated = connection.execute(
            "SELECT MAX(updated_at) FROM stocks"
        ).fetchone()[0]
    return {
        "stockCount": stock_count,
        "priceCount": price_count,
        "analysisCount": current_analysis_count,
        "detectedCount": detected_count,
        "lastUpdated": last_updated,
        "algorithmVersion": ALGORITHM_VERSION,
        "databasePath": DATABASE_PATH,
    }


def cached_analysis_results() -> list[dict]:
    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            """
            SELECT s.symbol, s.name, s.currency, s.listing_date, a.result_json
            FROM stocks s
            JOIN analyses a ON a.symbol = s.symbol
            WHERE a.algorithm_version = ?
            ORDER BY s.symbol
            """,
            (ALGORITHM_VERSION,),
        ).fetchall()
    results = []
    for row in rows:
        analysis = json.loads(row["result_json"])
        add_holding_performance_to_evaluations(
            analysis.get("bottomEvaluations") or [],
            load_cached_points(row["symbol"]),
        )
        evaluation = primary_bottom_evaluation(analysis)
        currency = row["currency"]
        results.append(
            {
                "input": row["symbol"],
                "symbol": row["symbol"],
                "name": row["name"],
                "currency": currency,
                "jpyRate": currency_to_jpy_rate(currency),
                "algorithmMode": analysis.get("algorithmMode", "general"),
                "detected": bool(analysis.get("detected")),
                "stableDate": (
                    evaluation.get("date") if evaluation else analysis.get("stableDate")
                ),
                "stablePrice": evaluation.get("price") if evaluation else None,
                "stablePriceJpy": to_jpy_amount(
                    evaluation.get("price") if evaluation else None,
                    currency,
                ),
                "listingDate": analysis.get("listingDate")
                or row["listing_date"],
                "calendarDaysToStable": analysis.get(
                    "calendarDaysToStable"
                ),
                "monthsToStable": analysis.get("monthsToStable"),
                "scoreAtStable": analysis.get("scoreAtStable"),
                "reason": analysis.get("reason"),
                "bottomEvaluation": evaluation,
                "drawdownAfterPercent": (
                    evaluation.get("drawdownAfterPercent")
                    if evaluation
                    else None
                ),
                "bottomVerdict": evaluation.get("verdict") if evaluation else None,
                "previousPeakDate": (
                    evaluation.get("previousPeakDate") if evaluation else None
                ),
                "previousPeakPrice": (
                    evaluation.get("previousPeakPrice") if evaluation else None
                ),
                "previousPeakPriceJpy": to_jpy_amount(
                    evaluation.get("previousPeakPrice") if evaluation else None,
                    currency,
                ),
                "drawdownFromPreviousPeakPercent": (
                    evaluation.get("drawdownFromPreviousPeakPercent")
                    if evaluation
                    else None
                ),
                "bottomPositionRatio": (
                    evaluation.get("bottomPositionRatio") if evaluation else None
                ),
                "minAfterDate": evaluation.get("minAfterDate") if evaluation else None,
                "minAfterPrice": (
                    evaluation.get("minAfterPrice") if evaluation else None
                ),
                "minAfterPriceJpy": to_jpy_amount(
                    evaluation.get("minAfterPrice") if evaluation else None,
                    currency,
                ),
                "maxBeforeActualBottomDate": (
                    evaluation.get("maxBeforeActualBottomDate")
                    if evaluation
                    else None
                ),
                "maxBeforeActualBottomPrice": (
                    evaluation.get("maxBeforeActualBottomPrice")
                    if evaluation
                    else None
                ),
                "maxBeforeActualBottomPriceJpy": to_jpy_amount(
                    evaluation.get("maxBeforeActualBottomPrice")
                    if evaluation
                    else None,
                    currency,
                ),
                "riseBeforeActualBottomPercent": (
                    evaluation.get("riseBeforeActualBottomPercent")
                    if evaluation
                    else None
                ),
                "currentDate": evaluation.get("currentDate") if evaluation else None,
                "currentPrice": evaluation.get("currentPrice") if evaluation else None,
                "currentPriceJpy": to_jpy_amount(
                    evaluation.get("currentPrice") if evaluation else None,
                    currency,
                ),
                "holdingReturnPercent": (
                    evaluation.get("holdingReturnPercent") if evaluation else None
                ),
                "annualizedReturnPercent": (
                    evaluation.get("annualizedReturnPercent") if evaluation else None
                ),
                "tradingDaysHeld": (
                    evaluation.get("tradingDaysHeld") if evaluation else None
                ),
                "calendarDaysHeld": (
                    evaluation.get("calendarDaysHeld") if evaluation else None
                ),
                "delayedBuyDays": (
                    evaluation.get("delayedBuyDays") if evaluation else None
                ),
                "delayedBuyDate": (
                    evaluation.get("delayedBuyDate") if evaluation else None
                ),
                "delayedBuyPrice": (
                    evaluation.get("delayedBuyPrice") if evaluation else None
                ),
                "delayedBuyPriceJpy": to_jpy_amount(
                    evaluation.get("delayedBuyPrice") if evaluation else None,
                    currency,
                ),
                "delayedHoldingReturnPercent": (
                    evaluation.get("delayedHoldingReturnPercent")
                    if evaluation
                    else None
                ),
                "delayedAnnualizedReturnPercent": (
                    evaluation.get("delayedAnnualizedReturnPercent")
                    if evaluation
                    else None
                ),
                "delayedTradingDaysHeld": (
                    evaluation.get("delayedTradingDaysHeld") if evaluation else None
                ),
                "delayedCalendarDaysHeld": (
                    evaluation.get("delayedCalendarDaysHeld") if evaluation else None
                ),
                "drawdownBuyPercent": (
                    evaluation.get("drawdownBuyPercent") if evaluation else None
                ),
                "drawdownBuyTargetPrice": (
                    evaluation.get("drawdownBuyTargetPrice") if evaluation else None
                ),
                "drawdownBuyTargetPriceJpy": to_jpy_amount(
                    evaluation.get("drawdownBuyTargetPrice") if evaluation else None,
                    currency,
                ),
                "drawdownBuyDate": (
                    evaluation.get("drawdownBuyDate") if evaluation else None
                ),
                "drawdownBuyPrice": (
                    evaluation.get("drawdownBuyPrice") if evaluation else None
                ),
                "drawdownBuyPriceJpy": to_jpy_amount(
                    evaluation.get("drawdownBuyPrice") if evaluation else None,
                    currency,
                ),
                "drawdownHoldingReturnPercent": (
                    evaluation.get("drawdownHoldingReturnPercent")
                    if evaluation
                    else None
                ),
                "drawdownAnnualizedReturnPercent": (
                    evaluation.get("drawdownAnnualizedReturnPercent")
                    if evaluation
                    else None
                ),
                "drawdownTradingDaysHeld": (
                    evaluation.get("drawdownTradingDaysHeld") if evaluation else None
                ),
                "drawdownCalendarDaysHeld": (
                    evaluation.get("drawdownCalendarDaysHeld") if evaluation else None
                ),
                "tradingDaysToMinAfter": (
                    evaluation.get("tradingDaysToMinAfter") if evaluation else None
                ),
                "calendarDaysToMinAfter": (
                    evaluation.get("calendarDaysToMinAfter") if evaluation else None
                ),
            }
        )
    return results


def search_symbols(keyword: str) -> list[dict]:
    keyword = keyword.strip().upper()
    if not keyword:
        return []
    candidates: dict[str, dict] = {}
    for item in SYMBOL_SEARCH_SEEDS:
        candidates[item["symbol"]] = item

    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            """
            SELECT symbol, name, exchange
            FROM stocks
            ORDER BY symbol
            """
        ).fetchall()
    for row in rows:
        candidates[row["symbol"]] = {
            "symbol": row["symbol"],
            "name": row["name"],
            "market": row["exchange"] or "保存済み",
        }

    matched = []
    for item in candidates.values():
        haystack = (
            f'{item["symbol"]} {item["name"]} {item.get("market", "")}'
        ).upper()
        if keyword in haystack:
            matched.append(item)
    return sorted(matched, key=lambda item: item["symbol"])[:20]


def normalize_search_text(value: str) -> str:
    text = value.strip().upper()
    text = text.translate(str.maketrans("ァィゥェォッャュョ", "アイウエオツヤユヨ"))
    text = re.sub(r"[\s　・･\-_.,/()（）【】\[\]]+", "", text)
    return text


def candidate_search_blob(item: dict) -> str:
    parts = [
        item.get("symbol", ""),
        item.get("name", ""),
        item.get("market", ""),
        " ".join(item.get("aliases", [])),
    ]
    return normalize_search_text(" ".join(parts))


def symbol_search_score(item: dict, raw_keyword: str) -> int | None:
    keyword = normalize_search_text(raw_keyword)
    if not keyword:
        return None
    symbol = normalize_search_text(item.get("symbol", ""))
    bare_symbol = symbol.replace(".T", "")
    name = normalize_search_text(item.get("name", ""))
    aliases = [normalize_search_text(alias) for alias in item.get("aliases", [])]
    blob = candidate_search_blob(item)
    score: int | None = None
    if keyword == symbol or keyword == bare_symbol:
        score = 0
    elif any(keyword == alias for alias in aliases):
        score = 1
    elif symbol.startswith(keyword) or bare_symbol.startswith(keyword):
        score = 2
    elif name.startswith(keyword):
        score = 3
    elif any(alias.startswith(keyword) for alias in aliases):
        score = 4
    elif keyword in blob:
        score = 8
    if score is None:
        return None
    if item.get("saved"):
        score -= 1
    if item.get("source") == "seed":
        score -= 1
    return max(score, 0)


def search_symbols(keyword: str) -> list[dict]:
    raw_keyword = keyword.strip()
    if not raw_keyword:
        return []
    candidates: dict[str, dict] = {}
    for item in SYMBOL_SEARCH_SEEDS:
        symbol = item["symbol"]
        candidates[symbol] = {
            **item,
            "aliases": SYMBOL_SEARCH_ALIASES.get(symbol, []),
            "source": "seed",
            "saved": False,
        }

    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            """
            SELECT symbol, name, exchange, updated_at
            FROM stocks
            ORDER BY updated_at DESC, symbol
            """
        ).fetchall()
    for row in rows:
        symbol = row["symbol"]
        existing = candidates.get(symbol, {})
        candidates[symbol] = {
            "symbol": symbol,
            "name": row["name"] or existing.get("name", symbol),
            "market": row["exchange"] or existing.get("market", "保存済み"),
            "aliases": list(
                dict.fromkeys(
                    [*existing.get("aliases", []), *SYMBOL_SEARCH_ALIASES.get(symbol, [])]
                )
            ),
            "source": existing.get("source", "cache"),
            "saved": True,
        }

    if re.fullmatch(r"[A-Za-z0-9.\-]{1,12}", raw_keyword.strip()):
        try:
            normalized_symbol = normalize_symbol(raw_keyword, "auto")
            if normalized_symbol not in candidates:
                candidates[normalized_symbol] = {
                    "symbol": normalized_symbol,
                    "name": "コードを直接指定",
                    "market": "直接入力",
                    "aliases": [raw_keyword],
                    "source": "direct",
                    "saved": False,
                }
        except Exception:
            pass

    matched = []
    for item in candidates.values():
        score = symbol_search_score(item, raw_keyword)
        if score is None:
            continue
        result = dict(item)
        result["score"] = score
        matched.append(result)
    matched.sort(
        key=lambda item: (
            item["score"],
            not item.get("saved", False),
            item.get("symbol", ""),
        )
    )
    return matched[:30]


def moving_average(values: list[float], window: int) -> list[float | None]:
    averages: list[float | None] = [None] * len(values)
    running_sum = 0.0
    for index, value in enumerate(values):
        running_sum += value
        if index >= window:
            running_sum -= values[index - window]
        if index >= window - 1:
            averages[index] = running_sum / window
    return averages


def clean_price_points(points: list[PricePoint]) -> list[PricePoint]:
    by_date: dict[str, PricePoint] = {}
    for point in points:
        if point.close > 0 and math.isfinite(point.close):
            by_date[point.date_text] = point
    return sorted(by_date.values(), key=lambda point: point.timestamp)


def parse_analysis_date(value: str | None, field_name: str) -> int | None:
    if not value:
        return None
    value = value.strip()
    if not value:
        return None
    try:
        parsed = datetime.strptime(value, "%Y-%m-%d")
    except ValueError as exc:
        raise ValueError(
            f"{field_name}は YYYY-MM-DD 形式で入力してください。"
        ) from exc
    return int(parsed.timestamp())


def slice_points_by_date(
    points: list[PricePoint],
    start_date: str | None = None,
    end_date: str | None = None,
) -> tuple[list[PricePoint], dict]:
    start_timestamp = parse_analysis_date(start_date, "分析開始日")
    end_timestamp = parse_analysis_date(end_date, "分析終了日")
    if end_timestamp is not None:
        end_timestamp += 86399
    if (
        start_timestamp is not None
        and end_timestamp is not None
        and start_timestamp > end_timestamp
    ):
        raise ValueError("分析開始日は分析終了日以前にしてください。")

    filtered = [
        point
        for point in clean_price_points(points)
        if (start_timestamp is None or point.timestamp >= start_timestamp)
        and (end_timestamp is None or point.timestamp <= end_timestamp)
    ]
    scope = {
        "custom": bool(start_date or end_date),
        "requestedStart": start_date or None,
        "requestedEnd": end_date or None,
        "effectiveStart": filtered[0].date_text if filtered else None,
        "effectiveEnd": filtered[-1].date_text if filtered else None,
        "tradingDays": len(filtered),
    }
    return filtered, scope


def fetch_manual_analysis_points(
    symbol: str,
    fallback_points: list[PricePoint],
    start_date: str | None = None,
    end_date: str | None = None,
) -> tuple[list[PricePoint], dict]:
    start_timestamp = parse_analysis_date(start_date, "分析開始日")
    end_timestamp = parse_analysis_date(end_date, "分析終了日")
    clean_fallback = clean_price_points(fallback_points)
    if start_timestamp is None:
        start_timestamp = (
            clean_fallback[0].timestamp if clean_fallback else 0
        )
    if end_timestamp is None:
        end_timestamp = int(time.time()) + 86400
    else:
        end_timestamp += 2 * 86400
    if start_timestamp > end_timestamp:
        raise ValueError("分析開始日は分析終了日以前にしてください。")

    try:
        fetched = fetch_history_range(
            symbol,
            max(0, start_timestamp - 86400),
            end_timestamp,
        )
        source_points = fetched.points
    except Exception:
        source_points = clean_fallback

    return slice_points_by_date(source_points, start_date, end_date)


def forward_performance(
    points: list[PricePoint],
    confirmation_index: int,
    windows: tuple[int, ...],
) -> dict:
    base = points[confirmation_index].close
    performance: dict[str, float | None] = {}
    for window in windows:
        end_index = confirmation_index + window
        if end_index >= len(points):
            performance[f"return{window}"] = None
            performance[f"mfe{window}"] = None
            performance[f"mae{window}"] = None
            continue
        future = points[confirmation_index + 1 : end_index + 1]
        performance[f"return{window}"] = round(
            (points[end_index].close / base - 1) * 100, 2
        )
        performance[f"mfe{window}"] = round(
            (max(point.close for point in future) / base - 1) * 100, 2
        )
        performance[f"mae{window}"] = round(
            (min(point.close for point in future) / base - 1) * 100, 2
        )
    return performance


def bottom_signal_evaluations(
    signals: list[dict], points: list[PricePoint]
) -> list[dict]:
    points = clean_price_points(points)
    by_date = {point.date_text: index for index, point in enumerate(points)}
    evaluations: list[dict] = []
    for order, signal in enumerate(signals, start=1):
        date_text = signal.get("confirmationDate")
        if date_text not in by_date:
            continue
        index = by_date[date_text]
        base_price = signal.get("confirmationClose") or points[index].close
        past = points[: index + 1]
        previous_peak_point = max(
            past,
            key=lambda point: (
                point.high if point.high is not None else point.close
            ),
        )
        previous_peak_price = (
            previous_peak_point.high
            if previous_peak_point.high is not None
            else previous_peak_point.close
        )
        future = points[index:]
        min_offset, min_point = min(
            enumerate(future),
            key=lambda item: (
                item[1].low if item[1].low is not None else item[1].close
            ),
        )
        min_price = min_point.low if min_point.low is not None else min_point.close
        before_bottom = future[: min_offset + 1]
        max_before_bottom_point = max(
            before_bottom,
            key=lambda point: (
                point.high if point.high is not None else point.close
            ),
        )
        max_before_bottom_price = (
            max_before_bottom_point.high
            if max_before_bottom_point.high is not None
            else max_before_bottom_point.close
        )
        drawdown_after = (
            (min_price / base_price - 1) * 100 if base_price else 0.0
        )
        drawdown_from_previous_peak = (
            (base_price / previous_peak_price - 1) * 100
            if previous_peak_price
            else 0.0
        )
        bottom_position_ratio = None
        denominator = previous_peak_price - min_price
        if denominator > 0:
            bottom_position_ratio = clamp(
                (base_price - min_price) / denominator
            )
        rebound_before_bottom = (
            (max_before_bottom_price / base_price - 1) * 100
            if base_price
            else 0.0
        )
        current_point = points[-1]
        current_price = current_point.close
        holding_return = (
            (current_price / base_price - 1) * 100 if base_price else 0.0
        )
        calendar_days_to_min = None
        calendar_days_held = None
        annualized_return = None
        try:
            candidate_date = datetime.strptime(date_text, "%Y-%m-%d")
            min_date = datetime.strptime(min_point.date_text, "%Y-%m-%d")
            calendar_days_to_min = (min_date - candidate_date).days
            current_date = datetime.strptime(current_point.date_text, "%Y-%m-%d")
            calendar_days_held = (current_date - candidate_date).days
            if calendar_days_held > 0 and base_price > 0 and current_price > 0:
                annualized_return = (
                    (current_price / base_price) ** (365.25 / calendar_days_held)
                    - 1
                ) * 100
        except ValueError:
            calendar_days_to_min = None
        if drawdown_after >= -5:
            verdict = "成功"
            verdict_detail = "候補日後の下押しが小さく、かなり良い位置でした。"
        elif drawdown_after >= -15:
            verdict = "許容"
            verdict_detail = "候補日後に少し下押ししましたが、底圏としては許容範囲です。"
        else:
            verdict = "早すぎ"
            verdict_detail = "候補日後に大きく下げており、底打ち判定が早すぎた可能性があります。"
        evaluations.append(
            {
                "index": order,
                "date": date_text,
                "price": round(base_price, 4),
                "triggerDate": signal.get("triggerDate"),
                "triggerType": signal.get("triggerType"),
                "previousPeakDate": previous_peak_point.date_text,
                "previousPeakPrice": round(previous_peak_price, 4),
                "drawdownFromPreviousPeakPercent": round(
                    drawdown_from_previous_peak, 2
                ),
                "minAfterDate": min_point.date_text,
                "minAfterPrice": round(min_price, 4),
                "drawdownAfterPercent": round(drawdown_after, 2),
                "bottomPositionRatio": (
                    round(bottom_position_ratio, 4)
                    if bottom_position_ratio is not None
                    else None
                ),
                "maxBeforeActualBottomDate": max_before_bottom_point.date_text,
                "maxBeforeActualBottomPrice": round(max_before_bottom_price, 4),
                "riseBeforeActualBottomPercent": round(
                    rebound_before_bottom, 2
                ),
                "currentDate": current_point.date_text,
                "currentPrice": round(current_price, 4),
                "holdingReturnPercent": round(holding_return, 2),
                "annualizedReturnPercent": (
                    round(annualized_return, 2)
                    if annualized_return is not None
                    else None
                ),
                "tradingDaysHeld": len(points) - 1 - index,
                "calendarDaysHeld": calendar_days_held,
                "tradingDaysToMinAfter": min_offset,
                "calendarDaysToMinAfter": calendar_days_to_min,
                "verdict": verdict,
                "verdictDetail": verdict_detail,
            }
        )
    return evaluations


def primary_bottom_evaluation(analysis: dict) -> dict | None:
    evaluations = analysis.get("bottomEvaluations") or []
    if not evaluations:
        return None
    return evaluations[-1]


def add_holding_performance_to_evaluations(
    evaluations: list[dict],
    points: list[PricePoint],
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
) -> None:
    points = clean_price_points(points)
    if not evaluations or not points:
        return
    delayed_buy_days = normalize_delayed_buy_days(delayed_buy_days)
    drawdown_buy_percent = normalize_drawdown_buy_percent(drawdown_buy_percent)
    by_date = {point.date_text: index for index, point in enumerate(points)}
    current_point = points[-1]
    current_price = current_point.close
    for evaluation in evaluations:
        date_text = evaluation.get("date")
        if date_text not in by_date:
            continue
        index = by_date[date_text]
        base_price = evaluation.get("price") or points[index].close
        holding_return = (
            (current_price / base_price - 1) * 100 if base_price else 0.0
        )
        calendar_days_held = None
        annualized_return = None
        try:
            candidate_date = datetime.strptime(date_text, "%Y-%m-%d")
            current_date = datetime.strptime(current_point.date_text, "%Y-%m-%d")
            calendar_days_held = (current_date - candidate_date).days
            if calendar_days_held > 0 and base_price > 0 and current_price > 0:
                annualized_return = (
                    (current_price / base_price) ** (365.25 / calendar_days_held)
                    - 1
                ) * 100
        except ValueError:
            calendar_days_held = None
        delayed_index = index + delayed_buy_days
        delayed_buy_point = (
            points[delayed_index]
            if delayed_buy_enabled and delayed_index < len(points)
            else None
        )
        delayed_calendar_days_held = None
        delayed_annualized_return = None
        delayed_holding_return = None
        if delayed_buy_point is not None:
            delayed_buy_price = delayed_buy_point.close
            delayed_holding_return = (
                (current_price / delayed_buy_price - 1) * 100
                if delayed_buy_price
                else 0.0
            )
            try:
                delayed_buy_date = datetime.strptime(
                    delayed_buy_point.date_text, "%Y-%m-%d"
                )
                current_date = datetime.strptime(current_point.date_text, "%Y-%m-%d")
                delayed_calendar_days_held = (current_date - delayed_buy_date).days
                if (
                    delayed_calendar_days_held > 0
                    and delayed_buy_price > 0
                    and current_price > 0
                ):
                    delayed_annualized_return = (
                        (current_price / delayed_buy_price)
                        ** (365.25 / delayed_calendar_days_held)
                        - 1
                    ) * 100
            except ValueError:
                delayed_calendar_days_held = None
        drawdown_target_price = (
            base_price * (1 + drawdown_buy_percent / 100)
            if base_price
            else None
        )
        drawdown_buy_index = None
        drawdown_buy_point = None
        drawdown_calendar_days_held = None
        drawdown_annualized_return = None
        drawdown_holding_return = None
        if drawdown_buy_enabled and drawdown_target_price is not None:
            for candidate_index in range(index, len(points)):
                candidate_point = points[candidate_index]
                candidate_low = (
                    candidate_point.low
                    if candidate_point.low is not None
                    else candidate_point.close
                )
                if candidate_low <= drawdown_target_price:
                    drawdown_buy_index = candidate_index
                    drawdown_buy_point = candidate_point
                    break
            if drawdown_buy_point is not None:
                drawdown_holding_return = (
                    (current_price / drawdown_target_price - 1) * 100
                    if drawdown_target_price
                    else 0.0
                )
                try:
                    drawdown_buy_date = datetime.strptime(
                        drawdown_buy_point.date_text, "%Y-%m-%d"
                    )
                    current_date = datetime.strptime(
                        current_point.date_text, "%Y-%m-%d"
                    )
                    drawdown_calendar_days_held = (
                        current_date - drawdown_buy_date
                    ).days
                    if (
                        drawdown_calendar_days_held > 0
                        and drawdown_target_price > 0
                        and current_price > 0
                    ):
                        drawdown_annualized_return = (
                            (current_price / drawdown_target_price)
                            ** (365.25 / drawdown_calendar_days_held)
                            - 1
                        ) * 100
                except ValueError:
                    drawdown_calendar_days_held = None
            elif drawdown_miss_zero_enabled:
                drawdown_holding_return = 0.0
        return_ranks = {
            "immediateBuyRank": None,
            "delayedBuyRank": None,
            "drawdownBuyRank": None,
        }
        if delayed_buy_enabled and drawdown_buy_enabled:
            rank_candidates = [
                ("immediateBuyRank", holding_return),
            ]
            if delayed_holding_return is not None:
                rank_candidates.append(("delayedBuyRank", delayed_holding_return))
            if drawdown_holding_return is not None:
                rank_candidates.append(("drawdownBuyRank", drawdown_holding_return))
            rank_candidates.sort(key=lambda item: item[1], reverse=True)
            for rank, (rank_key, _return_value) in enumerate(rank_candidates, start=1):
                return_ranks[rank_key] = rank
        evaluation.update(
            {
                "currentDate": current_point.date_text,
                "currentPrice": round(current_price, 4),
                "holdingReturnPercent": round(holding_return, 2),
                "annualizedReturnPercent": (
                    round(annualized_return, 2)
                    if annualized_return is not None
                    else None
                ),
                "tradingDaysHeld": len(points) - 1 - index,
                "calendarDaysHeld": calendar_days_held,
                "delayedBuyEnabled": bool(delayed_buy_enabled),
                "delayedBuyDays": delayed_buy_days if delayed_buy_enabled else None,
                "delayedBuyDate": (
                    delayed_buy_point.date_text if delayed_buy_point is not None else None
                ),
                "delayedBuyPrice": (
                    round(delayed_buy_point.close, 4)
                    if delayed_buy_point is not None
                    else None
                ),
                "delayedHoldingReturnPercent": (
                    round(delayed_holding_return, 2)
                    if delayed_holding_return is not None
                    else None
                ),
                "delayedAnnualizedReturnPercent": (
                    round(delayed_annualized_return, 2)
                    if delayed_annualized_return is not None
                    else None
                ),
                "delayedTradingDaysHeld": (
                    len(points) - 1 - delayed_index
                    if delayed_buy_point is not None
                    else None
                ),
                "delayedCalendarDaysHeld": delayed_calendar_days_held,
                "drawdownBuyEnabled": bool(drawdown_buy_enabled),
                "drawdownMissZeroEnabled": bool(drawdown_miss_zero_enabled),
                "drawdownBuyPercent": (
                    round(drawdown_buy_percent, 4)
                    if drawdown_buy_enabled
                    else None
                ),
                "drawdownBuyTargetPrice": (
                    round(drawdown_target_price, 4)
                    if drawdown_buy_enabled and drawdown_target_price is not None
                    else None
                ),
                "drawdownBuyDate": (
                    drawdown_buy_point.date_text
                    if drawdown_buy_point is not None
                    else None
                ),
                "drawdownBuyPrice": (
                    round(drawdown_target_price, 4)
                    if drawdown_buy_point is not None
                    and drawdown_target_price is not None
                    else None
                ),
                "drawdownHoldingReturnPercent": (
                    round(drawdown_holding_return, 2)
                    if drawdown_holding_return is not None
                    else None
                ),
                "drawdownAnnualizedReturnPercent": (
                    round(drawdown_annualized_return, 2)
                    if drawdown_annualized_return is not None
                    else None
                ),
                "drawdownTradingDaysHeld": (
                    len(points) - 1 - drawdown_buy_index
                    if drawdown_buy_index is not None
                    else None
                ),
                "drawdownCalendarDaysHeld": drawdown_calendar_days_held,
                **return_ranks,
            }
        )


def add_peak_warning_series(
    points: list[PricePoint], series: list[dict]
) -> int:
    points = clean_price_points(points)
    closes = [point.close for point in points]
    returns: list[float | None] = [None]
    for index in range(1, len(points)):
        returns.append((closes[index] / closes[index - 1] - 1) * 100)

    overheat_count = 0
    warning_count = 0
    for index, row in enumerate(series):
        row["peakScore"] = None
        row["peakOverheat"] = False
        row["peakCandidate"] = False
        if index < 120 or index >= len(points):
            continue

        close = closes[index]
        previous_120 = closes[index - 120:index]
        previous_20 = closes[index - 20:index]
        previous_10 = closes[index - 10:index]
        high_120 = max(previous_120)
        low_120 = min(previous_120)
        high_20 = max(previous_20)
        return_120 = (
            (close / closes[index - 120] - 1) * 100
            if closes[index - 120] > 0
            else 0.0
        )
        runup_from_low = (
            (close / low_120 - 1) * 100 if low_120 > 0 else 0.0
        )
        price_location = close / high_120 if high_120 > 0 else 0.0
        volatility_values = [
            abs(value)
            for value in returns[index - 20:index]
            if value is not None
        ]
        volatility20 = mean(volatility_values) if volatility_values else 0.0
        return_5 = (
            (close / closes[index - 5] - 1) * 100
            if index >= 5 and closes[index - 5] > 0
            else 0.0
        )
        ma25_now = row.get("ma25")
        ma25_past = series[index - 5].get("ma25") if index >= 5 else None
        ma_weakening = (
            ma25_now is not None
            and ma25_past is not None
            and ma25_now <= ma25_past * 1.01
        )
        near_high = price_location >= 0.90
        rollover = (
            close <= high_20 * 0.95
            or return_5 <= -5.0
            or ma_weakening
        )

        runup_score = 35 * clamp(max(return_120, runup_from_low) / 100)
        location_score = 25 * clamp((price_location - 0.75) / 0.20)
        volatility_score = 20 * clamp((volatility20 - 2.0) / 3.0)
        rollover_score = 20 if rollover else 0
        peak_score = round(
            runup_score
            + location_score
            + volatility_score
            + rollover_score,
            1,
        )
        peak_overheat = bool(
            peak_score >= 65
            and near_high
            and max(return_120, runup_from_low) >= 50
        )
        peak_candidate = bool(
            peak_score >= 70
            and near_high
            and max(return_120, runup_from_low) >= 50
            and rollover
        )
        row.update(
            {
                "peakScore": peak_score,
                "peakOverheat": peak_overheat,
                "peakCandidate": peak_candidate,
                "peakNearHigh": near_high,
                "peakRollover": rollover,
                "peakVolatility20": round(volatility20, 2),
                "peakRunupPercent": round(max(return_120, runup_from_low), 2),
            }
        )
        if peak_overheat:
            overheat_count += 1
        if peak_candidate:
            warning_count += 1
    return {"overheat": overheat_count, "warning": warning_count}


def analyze_stability(
    points: list[PricePoint],
    security_type: str = "stock",
    config: SignalConfig = DEFAULT_SIGNAL_CONFIG,
    analysis_scope: dict | None = None,
) -> dict:
    security_type = normalize_security_type(security_type)
    points = clean_price_points(points)
    scope = {
        "custom": False,
        "requestedStart": None,
        "requestedEnd": None,
        "effectiveStart": points[0].date_text if points else None,
        "effectiveEnd": points[-1].date_text if points else None,
        "tradingDays": len(points),
    }
    if analysis_scope:
        scope.update(analysis_scope)
    minimum_days = max(
        config.min_peak_history,
        config.range_window,
        config.breakout_window,
    ) + config.confirmation_days
    if len(points) < minimum_days:
        return {
            "detected": False,
            "reason": (
                f"判定には最低{minimum_days}営業日分の日足が必要です。"
                f"現在は{len(points)}営業日です。"
            ),
            "listingDate": points[0].date_text if points else None,
            "dataEndDate": points[-1].date_text if points else None,
            "securityType": security_type,
            "signals": [],
            "backtest": backtest_summary([]),
            "series": [],
            "config": stability_config_dict(config, security_type),
            "analysisScope": scope,
        }

    closes = [point.close for point in points]
    ma25 = moving_average(closes, SHORT_MA_DAYS)
    ma75 = moving_average(closes, LONG_MA_DAYS)
    returns: list[float | None] = [None]
    for index in range(1, len(points)):
        returns.append((closes[index] / closes[index - 1] - 1) * 100)

    drawdown_limit = (
        config.etf_drawdown_percent
        if security_type == "etf"
        else config.stock_drawdown_percent
    )
    peak_age_limit = (
        config.etf_min_peak_age
        if security_type == "etf"
        else config.stock_min_peak_age
    )
    start_index = max(
        config.min_peak_history,
        config.range_window + 1,
        config.volatility_window + 1,
        config.breakout_window,
    )
    setup_flags = [False] * len(points)
    setup_details: dict[int, dict] = {}
    series: list[dict] = []
    pending: list[dict] = []
    signals: list[dict] = []
    last_signal_index = -config.cooldown_days
    preliminary_count = 0

    for index, point in enumerate(points):
        row = {
            "date": point.date_text,
            "close": round(point.close, 6),
            "ma25": round(ma25[index], 6) if ma25[index] is not None else None,
            "ma75": round(ma75[index], 6) if ma75[index] is not None else None,
            "score": None,
            "eligible": False,
            "candidate": False,
            "priceTrigger": False,
            "triggerType": None,
        }
        if index < start_index:
            series.append(row)
            continue

        # セットアップは必ず前日までの情報だけで計算する。
        peak_start = max(0, index - config.peak_window)
        peak_slice = closes[peak_start:index]
        rolling_peak = max(peak_slice)
        peak_relative_indexes = [
            offset
            for offset, value in enumerate(peak_slice)
            if value == rolling_peak
        ]
        peak_index = peak_start + peak_relative_indexes[-1]
        peak_age = index - peak_index
        previous_close = closes[index - 1]
        recent_low = min(closes[index - config.range_window:index])
        close_drawdown = (1 - previous_close / rolling_peak) * 100
        recent_low_drawdown = (1 - recent_low / rolling_peak) * 100
        drawdown_pass = (
            close_drawdown >= drawdown_limit
            or recent_low_drawdown
            >= max(drawdown_limit, config.recent_low_drawdown_percent)
        )
        time_pass = peak_age >= peak_age_limit

        range_closes = closes[index - config.range_window:index]
        range_low = min(range_closes)
        range_high = max(range_closes)
        range_percent = (
            (range_high - range_low) / range_low * 100
            if range_low > 0
            else 100.0
        )
        range_pass = range_percent <= config.max_range_percent
        volatility_values = [
            abs(value)
            for value in returns[
                index - config.volatility_window:index
            ]
            if value is not None
        ]
        volatility = mean(volatility_values)
        volatility_pass = (
            volatility <= config.max_abs_return_percent
        )
        setup_pass = bool(
            drawdown_pass and time_pass and range_pass and volatility_pass
        )
        setup_flags[index] = setup_pass

        drawdown_score = 30 * clamp(
            close_drawdown / max(drawdown_limit, 1)
        )
        volatility_score = 20 * clamp(
            (config.max_abs_return_percent * 1.6 - volatility)
            / (config.max_abs_return_percent * 0.6)
        )
        range_score = 25 * clamp(
            (config.max_range_percent * 1.5 - range_percent)
            / (config.max_range_percent * 0.5)
        )
        base_score = drawdown_score + volatility_score + range_score
        setup_details[index] = {
            "rollingPeak": round(rolling_peak, 4),
            "peakDate": points[peak_index].date_text,
            "peakAgeTradingDays": peak_age,
            "peakAgeMonths": round(peak_age / 21, 1),
            "drawdownPercent": round(close_drawdown, 2),
            "recentLowDrawdownPercent": round(
                recent_low_drawdown, 2
            ),
            "range60": round(range_percent, 2),
            "volatility20": round(volatility, 2),
            "drawdownPass": drawdown_pass,
            "timePass": time_pass,
            "rangePass": range_pass,
            "volatilityPass": volatility_pass,
        }

        density_start = max(
            start_index, index - config.setup_density_window
        )
        setup_days = sum(setup_flags[density_start:index])
        setup_ready = setup_days >= config.setup_required_days
        prior_box_high = max(
            closes[index - config.breakout_window:index]
        )
        prior_short_high = max(
            closes[index - config.expansion_window:index]
        )
        daily_return = returns[index] or 0.0
        previous_volumes = [
            item.volume
            for item in points[
                index - config.volatility_window:index
            ]
            if item.volume is not None and item.volume > 0
        ]
        average_volume = (
            mean(previous_volumes)
            if len(previous_volumes) == config.volatility_window
            else None
        )
        volume_ratio = (
            point.volume / average_volume
            if point.volume is not None
            and point.volume > 0
            and average_volume
            else None
        )
        if (
            point.high is not None
            and point.low is not None
            and point.high > point.low
        ):
            close_strength = (
                (point.close - point.low) / (point.high - point.low)
            )
        else:
            close_strength = 0.0

        breakout_level = prior_box_high * (
            1 + config.breakout_buffer_percent / 100
        )
        expansion_level = prior_short_high * (
            1 + config.breakout_buffer_percent / 100
        )
        volume_breakout = bool(
            setup_ready
            and point.close >= breakout_level
            and daily_return >= config.breakout_min_return_percent
            and volume_ratio is not None
            and volume_ratio >= config.breakout_volume_ratio
            and close_strength >= config.close_strength_limit
        )
        volume_expansion = bool(
            setup_ready
            and point.close >= expansion_level
            and daily_return >= config.expansion_return_percent
            and volume_ratio is not None
            and volume_ratio >= config.expansion_volume_ratio
            and close_strength >= config.close_strength_limit
        )
        trigger_type = (
            "volume_breakout"
            if volume_breakout
            else "volume_expansion"
            if volume_expansion
            else None
        )
        if trigger_type:
            preliminary_count += 1
            pending.append(
                {
                    "index": index,
                    "date": point.date_text,
                    "close": point.close,
                    "level": (
                        breakout_level
                        if volume_breakout
                        else expansion_level
                    ),
                    "type": trigger_type,
                    "dailyReturn": daily_return,
                    "volumeRatio": volume_ratio,
                    "closeStrength": close_strength,
                    "setupIndex": index - 1,
                }
            )

        confirmed = None
        remaining = []
        for trigger in pending:
            age = index - trigger["index"]
            if age < config.confirmation_days:
                remaining.append(trigger)
                continue
            if age > config.confirmation_days:
                continue
            held = min(
                closes[trigger["index"]:index + 1]
            ) >= trigger["level"] * config.hold_tolerance
            followed = point.close >= trigger["close"]
            if (
                held
                and followed
                and index - last_signal_index >= config.cooldown_days
                and confirmed is None
            ):
                confirmed = trigger
        pending = remaining

        if confirmed:
            last_signal_index = index
            setup = setup_details[confirmed["setupIndex"]]
            signal = {
                "triggerDate": confirmed["date"],
                "confirmationDate": point.date_text,
                "triggerType": (
                    f'{confirmed["type"]}_confirmed'
                ),
                "triggerClose": round(confirmed["close"], 4),
                "confirmationClose": round(point.close, 4),
                "breakoutLevel": round(confirmed["level"], 4),
                "dailyReturn": round(confirmed["dailyReturn"], 2),
                "volumeRatio": round(confirmed["volumeRatio"], 2),
                "closeStrength": round(
                    confirmed["closeStrength"], 2
                ),
                **setup,
                **forward_performance(
                    points, index, config.forward_windows
                ),
            }
            signals.append(signal)

        row.update(
            {
                "score": round(
                    base_score + (25 if confirmed else 0), 1
                ),
                "eligible": setup_pass,
                "candidate": confirmed is not None,
                "priceTrigger": trigger_type is not None
                or confirmed is not None,
                "triggerType": (
                    f'{confirmed["type"]}_confirmed'
                    if confirmed
                    else trigger_type
                ),
            }
        )
        series.append(row)

    summary = backtest_summary(signals)
    peak_counts = add_peak_warning_series(points, series)
    bottom_evaluations = bottom_signal_evaluations(signals, points)
    result = {
        "detected": bool(signals),
        "listingDate": points[0].date_text,
        "dataEndDate": points[-1].date_text,
        "tradingDaysObserved": len(points),
        "securityType": security_type,
        "priceTriggerCount": preliminary_count,
        "peakOverheatCount": peak_counts["overheat"],
        "peakWarningCount": peak_counts["warning"],
        "signals": signals,
        "bottomEvaluations": bottom_evaluations,
        "backtest": summary,
        "series": series,
        "config": stability_config_dict(config, security_type),
        "analysisScope": scope,
    }
    if not signals:
        result["reason"] = (
            "過去500日高値からの大幅調整、日柄、底練り密度を"
            "満たした後の出来高付きブレイクと2日確認が"
            "見つかりませんでした。"
        )
        return result

    primary = signals[-1]
    confirmation_index = next(
        index
        for index, item in enumerate(points)
        if item.date_text == primary["confirmationDate"]
    )
    calendar_days = (
        points[confirmation_index].timestamp - points[0].timestamp
    ) // 86400
    result.update(
        {
            "stableDate": primary["confirmationDate"],
            "calendarDaysToStable": int(calendar_days),
            "tradingDaysToStable": confirmation_index,
            "monthsToStable": round(calendar_days / 30.4375, 1),
            "scoreAtStable": next(
                row["score"]
                for row in series
                if row["date"] == primary["confirmationDate"]
            ),
            "componentsAtStable": {
                "priceLocation": 30.0,
                "volatility": 20.0,
                "sideways": 25.0,
                "trend": 25.0,
            },
            "metricsAtStable": {
                "firstYearPeak": primary["rollingPeak"],
                "peakPriceRatio": round(
                    primary["triggerClose"]
                    / primary["rollingPeak"],
                    3,
                ),
                "drawdownPercent": primary["drawdownPercent"],
                "recentLowDrawdownPercent": primary[
                    "recentLowDrawdownPercent"
                ],
                "initialVolatility": None,
                "volatility20": primary["volatility20"],
                "volatilityRatio": None,
                "range60": primary["range60"],
                "boxHigh60": primary["breakoutLevel"],
                "breakoutLevel": primary["breakoutLevel"],
                "dailyReturn": primary["dailyReturn"],
                "volumeRatio": primary["volumeRatio"],
                "closeStrength": primary["closeStrength"],
                "triggerType": primary["triggerType"],
                "triggerEventDate": primary["triggerDate"],
                "peakDate": primary["peakDate"],
                "peakAgeTradingDays": primary[
                    "peakAgeTradingDays"
                ],
                "peakAgeMonths": primary["peakAgeMonths"],
                "confirmedAfterDays": config.confirmation_days,
            },
        }
    )
    return result


def analyze_ipo_stability(
    points: list[PricePoint],
    security_type: str = "stock",
    config: SignalConfig = DEFAULT_SIGNAL_CONFIG,
    analysis_scope: dict | None = None,
) -> dict:
    security_type = normalize_security_type(security_type)
    points = clean_price_points(points)
    scope = {
        "custom": False,
        "requestedStart": None,
        "requestedEnd": None,
        "effectiveStart": points[0].date_text if points else None,
        "effectiveEnd": points[-1].date_text if points else None,
        "tradingDays": len(points),
    }
    if analysis_scope:
        scope.update(analysis_scope)

    minimum_days = max(LONG_MA_DAYS, config.range_window) + config.confirmation_days
    if len(points) < minimum_days:
        return {
            "detected": False,
            "reason": (
                f"上場後特化判定には最低{minimum_days}営業日分の日足が必要です。"
                f"現在は{len(points)}営業日です。"
            ),
            "listingDate": points[0].date_text if points else None,
            "dataEndDate": points[-1].date_text if points else None,
            "securityType": security_type,
            "algorithmMode": "ipo",
            "signals": [],
            "backtest": backtest_summary([]),
            "series": [],
            "config": stability_config_dict(config, security_type, "ipo"),
            "analysisScope": scope,
        }

    first_timestamp = points[0].timestamp
    analysis_end_timestamp = first_timestamp + int(ANALYSIS_MAX_YEARS * 366 * 86400)
    analysis_points = [
        point for point in points if point.timestamp <= analysis_end_timestamp
    ]
    if len(analysis_points) < minimum_days:
        analysis_points = points
    points = analysis_points
    closes = [point.close for point in points]
    ma25 = moving_average(closes, SHORT_MA_DAYS)
    ma75 = moving_average(closes, LONG_MA_DAYS)
    returns: list[float | None] = [None]
    for index in range(1, len(points)):
        returns.append((closes[index] / closes[index - 1] - 1) * 100)

    first_year_end = first_timestamp + FIRST_YEAR_CALENDAR_DAYS * 86400
    first_year_points = [
        point for point in points if point.timestamp <= first_year_end
    ] or points[: min(len(points), 252)]
    first_year_peak = max(
        point.high if point.high is not None else point.close
        for point in first_year_points
    )
    first_year_peak_index = max(
        index
        for index, point in enumerate(points)
        if point.timestamp <= first_year_end
        and (point.high if point.high is not None else point.close)
        == first_year_peak
    )
    first_peak_age_min = 60
    start_index = max(
        LONG_MA_DAYS,
        config.range_window + 1,
        config.volatility_window + 1,
        config.breakout_window,
    )
    setup_flags = [False] * len(points)
    setup_details: dict[int, dict] = {}
    series: list[dict] = []
    pending: list[dict] = []
    signals: list[dict] = []
    last_signal_index = -config.cooldown_days
    preliminary_count = 0

    for index, point in enumerate(points):
        row = {
            "date": point.date_text,
            "close": round(point.close, 6),
            "ma25": round(ma25[index], 6) if ma25[index] is not None else None,
            "ma75": round(ma75[index], 6) if ma75[index] is not None else None,
            "score": None,
            "eligible": False,
            "candidate": False,
            "priceTrigger": False,
            "triggerType": None,
        }
        if index < start_index:
            series.append(row)
            continue

        previous_close = closes[index - 1]
        high_values = [
            item.high if item.high is not None else item.close
            for item in points[:index]
        ]
        rolling_peak = max(high_values)
        rolling_peak_index = max(
            offset
            for offset, value in enumerate(high_values)
            if value == rolling_peak
        )
        trough_after_peak = min(closes[rolling_peak_index:index])
        peak_age = index - rolling_peak_index
        close_drawdown = (1 - previous_close / rolling_peak) * 100
        max_drawdown_after_peak = (
            (1 - trough_after_peak / rolling_peak) * 100
            if rolling_peak > 0
            else 0.0
        )
        range_closes = closes[index - config.range_window:index]
        range_low = min(range_closes)
        range_high = max(range_closes)
        range_percent = (
            (range_high - range_low) / range_low * 100
            if range_low > 0
            else 100.0
        )
        volatility_values = [
            abs(value)
            for value in returns[index - config.volatility_window:index]
            if value is not None
        ]
        volatility = mean(volatility_values)
        drawdown_pass = (
            max_drawdown_after_peak
            >= (1 - PEAK_PRICE_RATIO_LIMIT) * 100
        )
        time_pass = peak_age >= first_peak_age_min
        range_pass = range_percent <= 40.0
        volatility_pass = volatility <= 3.5
        setup_pass = bool(
            drawdown_pass and time_pass and range_pass and volatility_pass
        )
        setup_flags[index] = setup_pass

        drawdown_score = 30 * clamp(
            max_drawdown_after_peak
            / ((1 - PEAK_PRICE_RATIO_LIMIT) * 100)
        )
        volatility_score = 20 * clamp(
            (VOLATILITY_ABS_RETURN_LIMIT * 1.6 - volatility)
            / (VOLATILITY_ABS_RETURN_LIMIT * 0.6)
        )
        range_score = 25 * clamp(
            (config.max_range_percent * 1.5 - range_percent)
            / (config.max_range_percent * 0.5)
        )
        base_score = drawdown_score + volatility_score + range_score
        setup_details[index] = {
            "rollingPeak": round(rolling_peak, 4),
            "peakDate": points[rolling_peak_index].date_text,
            "peakAgeTradingDays": peak_age,
            "peakAgeMonths": round(peak_age / 21, 1),
            "drawdownPercent": round(close_drawdown, 2),
            "recentLowDrawdownPercent": round(
                max_drawdown_after_peak, 2
            ),
            "range60": round(range_percent, 2),
            "volatility20": round(volatility, 2),
            "drawdownPass": drawdown_pass,
            "timePass": time_pass,
            "rangePass": range_pass,
            "volatilityPass": volatility_pass,
        }

        density_start = max(start_index, index - config.setup_density_window)
        setup_days = sum(setup_flags[density_start:index])
        setup_ready = setup_days >= 6
        prior_box_high = max(closes[index - config.breakout_window:index])
        prior_short_high = max(closes[index - config.expansion_window:index])
        daily_return = returns[index] or 0.0
        previous_volumes = [
            item.volume
            for item in points[index - config.volatility_window:index]
            if item.volume is not None and item.volume > 0
        ]
        average_volume = (
            mean(previous_volumes)
            if len(previous_volumes) == config.volatility_window
            else None
        )
        volume_ratio = (
            point.volume / average_volume
            if point.volume is not None and point.volume > 0 and average_volume
            else None
        )
        if point.high is not None and point.low is not None and point.high > point.low:
            close_strength = (point.close - point.low) / (point.high - point.low)
        else:
            close_strength = 0.0

        breakout_level = prior_box_high * (1 + config.breakout_buffer_percent / 100)
        expansion_level = prior_short_high * (1 + config.breakout_buffer_percent / 100)
        volume_ok_breakout = (
            volume_ratio is None or volume_ratio >= config.breakout_volume_ratio
        )
        volume_ok_expansion = (
            volume_ratio is None or volume_ratio >= config.expansion_volume_ratio
        )
        volume_breakout = bool(
            setup_ready
            and point.close >= breakout_level
            and daily_return >= config.breakout_min_return_percent
            and volume_ok_breakout
            and close_strength >= config.close_strength_limit
        )
        volume_expansion = bool(
            setup_ready
            and point.close >= expansion_level
            and daily_return >= config.expansion_return_percent
            and volume_ok_expansion
            and close_strength >= config.close_strength_limit
        )
        trigger_type = (
            "ipo_breakout"
            if volume_breakout
            else "ipo_expansion"
            if volume_expansion
            else None
        )
        if trigger_type:
            preliminary_count += 1
            pending.append(
                {
                    "index": index,
                    "date": point.date_text,
                    "close": point.close,
                    "level": breakout_level if volume_breakout else expansion_level,
                    "type": trigger_type,
                    "dailyReturn": daily_return,
                    "volumeRatio": volume_ratio,
                    "closeStrength": close_strength,
                    "setupIndex": index - 1,
                }
            )

        confirmed = None
        remaining = []
        for trigger in pending:
            age = index - trigger["index"]
            if age < config.confirmation_days:
                remaining.append(trigger)
                continue
            if age > config.confirmation_days:
                continue
            held = min(closes[trigger["index"]:index + 1]) >= (
                trigger["level"] * config.hold_tolerance
            )
            followed = point.close >= trigger["close"]
            if (
                held
                and followed
                and index - last_signal_index >= config.cooldown_days
                and confirmed is None
            ):
                confirmed = trigger
        pending = remaining

        if confirmed:
            last_signal_index = index
            setup = setup_details[confirmed["setupIndex"]]
            volume_value = confirmed["volumeRatio"]
            signal = {
                "triggerDate": confirmed["date"],
                "confirmationDate": point.date_text,
                "triggerType": f'{confirmed["type"]}_confirmed',
                "triggerClose": round(confirmed["close"], 4),
                "confirmationClose": round(point.close, 4),
                "breakoutLevel": round(confirmed["level"], 4),
                "dailyReturn": round(confirmed["dailyReturn"], 2),
                "volumeRatio": round(volume_value, 2) if volume_value else None,
                "closeStrength": round(confirmed["closeStrength"], 2),
                **setup,
                **forward_performance(points, index, config.forward_windows),
            }
            signals.append(signal)

        row.update(
            {
                "score": round(base_score + (25 if confirmed else 0), 1),
                "eligible": setup_pass,
                "candidate": confirmed is not None,
                "priceTrigger": trigger_type is not None or confirmed is not None,
                "triggerType": (
                    f'{confirmed["type"]}_confirmed' if confirmed else trigger_type
                ),
            }
        )
        series.append(row)

    peak_counts = add_peak_warning_series(points, series)
    bottom_evaluations = bottom_signal_evaluations(signals, points)
    result = {
        "detected": bool(signals),
        "listingDate": points[0].date_text,
        "dataEndDate": points[-1].date_text,
        "tradingDaysObserved": len(points),
        "securityType": security_type,
        "algorithmMode": "ipo",
        "priceTriggerCount": preliminary_count,
        "peakOverheatCount": peak_counts["overheat"],
        "peakWarningCount": peak_counts["warning"],
        "signals": signals,
        "bottomEvaluations": bottom_evaluations,
        "backtest": backtest_summary(signals),
        "series": series,
        "config": stability_config_dict(config, security_type, "ipo"),
        "analysisScope": scope,
    }
    if not signals:
        result["reason"] = (
            "上場後1年高値からの大幅下落、底練り密度、"
            "価格ブレイクと2日確認が揃いませんでした。"
        )
        return result

    primary = signals[-1]
    confirmation_index = next(
        index
        for index, item in enumerate(points)
        if item.date_text == primary["confirmationDate"]
    )
    calendar_days = (
        points[confirmation_index].timestamp - points[0].timestamp
    ) // 86400
    result.update(
        {
            "stableDate": primary["confirmationDate"],
            "calendarDaysToStable": int(calendar_days),
            "tradingDaysToStable": confirmation_index,
            "monthsToStable": round(calendar_days / 30.4375, 1),
            "scoreAtStable": next(
                row["score"]
                for row in series
                if row["date"] == primary["confirmationDate"]
            ),
            "componentsAtStable": {
                "priceLocation": 30.0,
                "volatility": 20.0,
                "sideways": 25.0,
                "trend": 25.0,
            },
            "metricsAtStable": {
                "firstYearPeak": primary["rollingPeak"],
                "peakPriceRatio": round(
                    primary["triggerClose"] / primary["rollingPeak"], 3
                ),
                "drawdownPercent": primary["drawdownPercent"],
                "recentLowDrawdownPercent": primary[
                    "recentLowDrawdownPercent"
                ],
                "initialVolatility": None,
                "volatility20": primary["volatility20"],
                "volatilityRatio": None,
                "range60": primary["range60"],
                "boxHigh60": primary["breakoutLevel"],
                "breakoutLevel": primary["breakoutLevel"],
                "dailyReturn": primary["dailyReturn"],
                "volumeRatio": primary["volumeRatio"],
                "closeStrength": primary["closeStrength"],
                "triggerType": primary["triggerType"],
                "triggerEventDate": primary["triggerDate"],
                "peakDate": primary["peakDate"],
                "peakAgeTradingDays": primary["peakAgeTradingDays"],
                "peakAgeMonths": primary["peakAgeMonths"],
                "confirmedAfterDays": config.confirmation_days,
            },
        }
    )
    return result


def analyze_bottoming(
    points: list[PricePoint],
    security_type: str = "stock",
    mode: str = "general",
    analysis_scope: dict | None = None,
) -> dict:
    mode = normalize_algorithm_mode(mode)
    if mode == "ipo":
        return analyze_ipo_stability(
            points, security_type, analysis_scope=analysis_scope
        )
    result = analyze_stability(
        points, security_type, analysis_scope=analysis_scope
    )
    result["algorithmMode"] = "general"
    result["config"]["algorithmMode"] = "general"
    return result


def backtest_summary(signals: list[dict]) -> dict:
    summary: dict[str, int | float | None] = {
        "signalCount": len(signals)
    }
    for window in (5, 20, 60):
        values = [
            signal.get(f"return{window}")
            for signal in signals
            if signal.get(f"return{window}") is not None
        ]
        summary[f"evaluated{window}"] = len(values)
        summary[f"averageReturn{window}"] = (
            round(mean(values), 2) if values else None
        )
        summary[f"winRate{window}"] = (
            round(
                sum(value > 0 for value in values)
                / len(values)
                * 100,
                1,
            )
            if values
            else None
        )
    return summary


def stability_config_dict(
    config: SignalConfig = DEFAULT_SIGNAL_CONFIG,
    security_type: str = "stock",
    mode: str = "general",
) -> dict:
    security_type = normalize_security_type(security_type)
    mode = normalize_algorithm_mode(mode)
    drawdown_limit = (
        config.etf_drawdown_percent
        if security_type == "etf"
        else config.stock_drawdown_percent
    )
    peak_age_limit = (
        config.etf_min_peak_age
        if security_type == "etf"
        else config.stock_min_peak_age
    )
    return {
        "algorithmMode": mode,
        "securityType": security_type,
        "peakWindow": config.peak_window,
        "minPeakHistory": config.min_peak_history,
        "drawdownPercent": drawdown_limit,
        "minimumPeakAge": peak_age_limit,
        "volatilityWindow": config.volatility_window,
        "initialVolatilityDays": INITIAL_VOLATILITY_DAYS,
        "sidewaysWindow": config.range_window,
        "shortMaDays": SHORT_MA_DAYS,
        "longMaDays": LONG_MA_DAYS,
        "firstYearCalendarDays": (
            FIRST_YEAR_CALENDAR_DAYS if mode == "ipo" else None
        ),
        "peakPriceRatioLimit": (
            PEAK_PRICE_RATIO_LIMIT
            if mode == "ipo"
            else round(1 - drawdown_limit / 100, 3)
        ),
        "volatilityAbsReturnLimit": (
            3.5 if mode == "ipo" else config.max_abs_return_percent
        ),
        "idealRangeWidth": config.ideal_range_percent,
        "rangeWidthLimit": 40.0 if mode == "ipo" else config.max_range_percent,
        "setupLookbackDays": config.setup_lookback_days,
        "setupDensityWindow": config.setup_density_window,
        "setupRequiredDays": 6 if mode == "ipo" else config.setup_required_days,
        "breakoutWindow": config.breakout_window,
        "expansionBreakoutWindow": config.expansion_window,
        "breakoutBufferPercent": config.breakout_buffer_percent,
        "breakoutMinReturnPercent": config.breakout_min_return_percent,
        "expansionReturnPercent": config.expansion_return_percent,
        "breakoutVolumeRatio": config.breakout_volume_ratio,
        "expansionVolumeRatio": config.expansion_volume_ratio,
        "closeStrengthLimit": config.close_strength_limit,
        "triggerConfirmDays": config.confirmation_days,
        "breakoutHoldTolerance": config.hold_tolerance,
        "cooldownDays": config.cooldown_days,
        "scoreThreshold": STABILITY_SCORE_THRESHOLD,
        "analysisMaxYears": ANALYSIS_MAX_YEARS,
    }


def basic_result_dict(result: StockResult) -> dict:
    points = result.points
    latest = points[-1]
    high_point = max(
        points, key=lambda point: point.high if point.high is not None else point.close
    )
    low_point = min(
        points, key=lambda point: point.low if point.low is not None else point.close
    )
    high_price = high_point.high if high_point.high is not None else high_point.close
    low_price = low_point.low if low_point.low is not None else low_point.close
    first_close = points[0].close
    change_percent = ((latest.close / first_close) - 1) * 100 if first_close else 0

    return {
        "symbol": result.symbol,
        "name": result.name,
        "currency": result.currency,
        "exchange": result.exchange,
        "securityType": result.security_type,
        "latest": {"price": latest.close, "date": latest.date_text},
        "highest": {"price": high_price, "date": high_point.date_text},
        "lowest": {"price": low_price, "date": low_point.date_text},
        "changePercent": change_percent,
        "points": [
            {
                "date": point.date_text,
                "close": point.close,
                "high": point.high,
                "low": point.low,
                "volume": point.volume,
            }
            for point in points
        ],
    }


def build_stock_payload(
    symbol: str,
    period: str,
    security_type: str = "stock",
    analysis_start: str | None = None,
    analysis_end: str | None = None,
    algorithm_mode: str = "general",
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
) -> dict:
    security_type = normalize_security_type(security_type)
    algorithm_mode = normalize_algorithm_mode(algorithm_mode)
    delayed_buy_days = normalize_delayed_buy_days(delayed_buy_days)
    drawdown_buy_percent = normalize_drawdown_buy_percent(drawdown_buy_percent)
    try:
        display_result = replace(
            fetch_stock_data(symbol, period),
            security_type=security_type,
        )
    except Exception:
        cached_result = cached_stock_result(symbol)
        if cached_result is None:
            raise
        display_result = cached_result

    listing_result, analysis, changed = ensure_symbol_cache(
        symbol,
        metadata=display_result,
        update_missing=True,
        security_type=security_type,
        history_scope="long" if algorithm_mode == "general" else "ipo",
    )
    if analysis_start or analysis_end:
        manual_base_points = (
            display_result.points + listing_result.points
        )
        ranged_points, scope = fetch_manual_analysis_points(
            symbol,
            manual_base_points,
            analysis_start,
            analysis_end,
        )
        analysis = analyze_bottoming(
            ranged_points,
            listing_result.security_type,
            algorithm_mode,
            analysis_scope=scope,
        )
    elif algorithm_mode != "general":
        analysis = analyze_bottoming(
            listing_result.points,
            listing_result.security_type,
            algorithm_mode,
        )
    add_holding_performance_to_evaluations(
        analysis.get("bottomEvaluations") or [],
        listing_result.points,
        delayed_buy_days,
        delayed_buy_enabled,
        drawdown_buy_percent,
        drawdown_buy_enabled,
        drawdown_miss_zero_enabled,
    )
    benchmark = benchmark_history()
    add_benchmark_performance_to_evaluations(
        analysis.get("bottomEvaluations") or [],
        benchmark.points if benchmark else None,
    )
    event_start = display_result.points[0].date_text if display_result.points else None
    event_end = display_result.points[-1].date_text if display_result.points else None
    important_events = annotate_important_events(
        important_events_for_display(symbol, event_start, event_end),
        display_result.points,
    )
    analysis["importantEvents"] = annotate_important_events(
        important_events_for_display(
            symbol,
            analysis.get("analysisScope", {}).get("effectiveStart")
            or listing_result.points[0].date_text,
            analysis.get("analysisScope", {}).get("effectiveEnd")
            or listing_result.points[-1].date_text,
        ),
        listing_result.points,
    )
    payload = basic_result_dict(display_result)
    payload["importantEvents"] = important_events
    payload["stability"] = analysis
    payload["cache"] = {
        "saved": True,
        "updated": changed,
        "savedPriceCount": len(listing_result.points),
        "algorithmVersion": ALGORITHM_VERSION,
    }
    return payload


def days_between_dates(start_date: str | None, end_date: str | None) -> int | None:
    if not start_date or not end_date:
        return None
    try:
        return (
            datetime.strptime(end_date, "%Y-%m-%d")
            - datetime.strptime(start_date, "%Y-%m-%d")
        ).days
    except ValueError:
        return None


def normalize_delayed_buy_days(value: object = None) -> int:
    if value in (None, ""):
        return DEFAULT_DELAYED_BUY_DAYS
    try:
        days = int(str(value).strip())
    except ValueError as exc:
        raise ValueError("遅延買付日数は0以上の整数で入力してください。") from exc
    if days < 0:
        raise ValueError("遅延買付日数は0以上で入力してください。")
    if days > 5000:
        raise ValueError("遅延買付日数は5000営業日以内で入力してください。")
    return days


def normalize_drawdown_buy_percent(value: object = None) -> float:
    if value in (None, ""):
        return DEFAULT_DRAWDOWN_BUY_PERCENT
    try:
        percent = float(str(value).strip())
    except ValueError as exc:
        raise ValueError("下落待ち買付率は数値で入力してください。") from exc
    if percent > 0:
        percent = -percent
    if percent <= -100:
        raise ValueError("下落待ち買付率は-100%より大きい値にしてください。")
    if percent > 0:
        raise ValueError("下落待ち買付率は0以下で入力してください。")
    return percent


def request_bool(value: object, default: bool = True) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    normalized = str(value).strip().lower()
    if normalized in {"1", "true", "yes", "on"}:
        return True
    if normalized in {"0", "false", "no", "off"}:
        return False
    return default


def batch_result_from_analysis(
    raw_symbol: str,
    history: StockResult,
    analysis: dict,
    mode: str,
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
) -> dict:
    with batch_timing_step("買い方別リターン計算"):
        add_holding_performance_to_evaluations(
            analysis.get("bottomEvaluations") or [],
            history.points,
            delayed_buy_days,
            delayed_buy_enabled,
            drawdown_buy_percent,
            drawdown_buy_enabled,
            drawdown_miss_zero_enabled,
        )
    with batch_timing_step("オルカン相当データ取得"):
        benchmark = benchmark_history()
    with batch_timing_step("オルカン相当リターン計算"):
        add_benchmark_performance_to_evaluations(
            analysis.get("bottomEvaluations") or [],
            benchmark.points if benchmark else None,
        )
    evaluation = primary_bottom_evaluation(analysis)
    display_stable_date = (
        evaluation.get("date") if evaluation else analysis.get("stableDate")
    )
    listing_date = analysis.get("listingDate")
    calendar_days = days_between_dates(listing_date, display_stable_date)
    if calendar_days is None:
        calendar_days = analysis.get("calendarDaysToStable")
    stable_price = evaluation.get("price") if evaluation else None
    current_price = evaluation.get("currentPrice") if evaluation else None
    if current_price is None and history.points:
        current_price = history.points[-1].close
    with batch_timing_step("時価総額取得・底検知時推定"):
        bottom_market_cap_jpy, current_market_cap_jpy, market_cap_currency = (
            estimated_market_cap_at_price_jpy(
                history.symbol,
                stable_price,
                current_price,
                history.currency,
            )
            if evaluation
            else (None, None, "")
        )
    with batch_timing_step("為替円換算"):
        jpy_rate = currency_to_jpy_rate(history.currency)
        stable_price_jpy = to_jpy_amount(stable_price, history.currency)
        previous_peak_price_jpy = to_jpy_amount(
            evaluation.get("previousPeakPrice") if evaluation else None,
            history.currency,
        )
        min_after_price_jpy = to_jpy_amount(
            evaluation.get("minAfterPrice") if evaluation else None,
            history.currency,
        )
        max_before_actual_bottom_price_jpy = to_jpy_amount(
            evaluation.get("maxBeforeActualBottomPrice") if evaluation else None,
            history.currency,
        )
        current_price_jpy = to_jpy_amount(current_price, history.currency)
        delayed_buy_price_jpy = to_jpy_amount(
            evaluation.get("delayedBuyPrice") if evaluation else None,
            history.currency,
        )
        drawdown_buy_target_price_jpy = to_jpy_amount(
            evaluation.get("drawdownBuyTargetPrice") if evaluation else None,
            history.currency,
        )
        drawdown_buy_price_jpy = to_jpy_amount(
            evaluation.get("drawdownBuyPrice") if evaluation else None,
            history.currency,
        )
    return {
        "input": raw_symbol,
        "symbol": history.symbol,
        "name": history.name,
        "currency": history.currency,
        "jpyRate": jpy_rate,
        "securityType": history.security_type,
        "algorithmMode": mode,
        "detected": analysis["detected"],
        "stableDate": display_stable_date,
        "stablePrice": stable_price,
        "stablePriceJpy": stable_price_jpy,
        "estimatedMarketCapAtBottomJpy": bottom_market_cap_jpy,
        "currentMarketCapJpy": current_market_cap_jpy,
        "marketCapCurrency": market_cap_currency,
        "listingDate": listing_date,
        "calendarDaysToStable": calendar_days,
        "monthsToStable": (
            round(calendar_days / 30.4375, 1)
            if calendar_days is not None
            else analysis.get("monthsToStable")
        ),
        "scoreAtStable": analysis.get("scoreAtStable"),
        "reason": analysis.get("reason"),
        "bottomEvaluation": evaluation,
        "drawdownAfterPercent": (
            evaluation.get("drawdownAfterPercent") if evaluation else None
        ),
        "bottomVerdict": evaluation.get("verdict") if evaluation else None,
        "previousPeakDate": (
            evaluation.get("previousPeakDate") if evaluation else None
        ),
        "previousPeakPrice": (
            evaluation.get("previousPeakPrice") if evaluation else None
        ),
        "previousPeakPriceJpy": previous_peak_price_jpy,
        "drawdownFromPreviousPeakPercent": (
            evaluation.get("drawdownFromPreviousPeakPercent")
            if evaluation
            else None
        ),
        "bottomPositionRatio": (
            evaluation.get("bottomPositionRatio") if evaluation else None
        ),
        "minAfterDate": evaluation.get("minAfterDate") if evaluation else None,
        "minAfterPrice": evaluation.get("minAfterPrice") if evaluation else None,
        "minAfterPriceJpy": min_after_price_jpy,
        "maxBeforeActualBottomDate": (
            evaluation.get("maxBeforeActualBottomDate") if evaluation else None
        ),
        "maxBeforeActualBottomPrice": (
            evaluation.get("maxBeforeActualBottomPrice") if evaluation else None
        ),
        "maxBeforeActualBottomPriceJpy": max_before_actual_bottom_price_jpy,
        "riseBeforeActualBottomPercent": (
            evaluation.get("riseBeforeActualBottomPercent") if evaluation else None
        ),
        "currentDate": evaluation.get("currentDate") if evaluation else None,
        "currentPrice": current_price,
        "currentPriceJpy": current_price_jpy,
        "holdingReturnPercent": (
            evaluation.get("holdingReturnPercent") if evaluation else None
        ),
        "immediateBuyRank": (
            evaluation.get("immediateBuyRank") if evaluation else None
        ),
        "annualizedReturnPercent": (
            evaluation.get("annualizedReturnPercent") if evaluation else None
        ),
        "tradingDaysHeld": evaluation.get("tradingDaysHeld") if evaluation else None,
        "calendarDaysHeld": evaluation.get("calendarDaysHeld") if evaluation else None,
        "delayedBuyDays": evaluation.get("delayedBuyDays") if evaluation else None,
        "delayedBuyDate": evaluation.get("delayedBuyDate") if evaluation else None,
        "delayedBuyPrice": evaluation.get("delayedBuyPrice") if evaluation else None,
        "delayedBuyPriceJpy": delayed_buy_price_jpy,
        "delayedHoldingReturnPercent": (
            evaluation.get("delayedHoldingReturnPercent") if evaluation else None
        ),
        "delayedBuyRank": evaluation.get("delayedBuyRank") if evaluation else None,
        "delayedAnnualizedReturnPercent": (
            evaluation.get("delayedAnnualizedReturnPercent") if evaluation else None
        ),
        "delayedTradingDaysHeld": (
            evaluation.get("delayedTradingDaysHeld") if evaluation else None
        ),
        "delayedCalendarDaysHeld": (
            evaluation.get("delayedCalendarDaysHeld") if evaluation else None
        ),
        "drawdownBuyPercent": evaluation.get("drawdownBuyPercent") if evaluation else None,
        "drawdownMissZeroEnabled": (
            evaluation.get("drawdownMissZeroEnabled") if evaluation else None
        ),
        "drawdownBuyTargetPrice": (
            evaluation.get("drawdownBuyTargetPrice") if evaluation else None
        ),
        "drawdownBuyTargetPriceJpy": drawdown_buy_target_price_jpy,
        "drawdownBuyDate": evaluation.get("drawdownBuyDate") if evaluation else None,
        "drawdownBuyPrice": evaluation.get("drawdownBuyPrice") if evaluation else None,
        "drawdownBuyPriceJpy": drawdown_buy_price_jpy,
        "drawdownHoldingReturnPercent": (
            evaluation.get("drawdownHoldingReturnPercent") if evaluation else None
        ),
        "drawdownBuyRank": (
            evaluation.get("drawdownBuyRank") if evaluation else None
        ),
        "drawdownAnnualizedReturnPercent": (
            evaluation.get("drawdownAnnualizedReturnPercent") if evaluation else None
        ),
        "benchmarkSymbol": evaluation.get("benchmarkSymbol") if evaluation else None,
        "benchmarkLabel": evaluation.get("benchmarkLabel") if evaluation else None,
        "benchmarkBuyDate": evaluation.get("benchmarkBuyDate") if evaluation else None,
        "benchmarkBuyPrice": evaluation.get("benchmarkBuyPrice") if evaluation else None,
        "benchmarkCurrentDate": (
            evaluation.get("benchmarkCurrentDate") if evaluation else None
        ),
        "benchmarkCurrentPrice": (
            evaluation.get("benchmarkCurrentPrice") if evaluation else None
        ),
        "benchmarkHoldingReturnPercent": (
            evaluation.get("benchmarkHoldingReturnPercent") if evaluation else None
        ),
        "benchmarkBuyRank": evaluation.get("benchmarkBuyRank") if evaluation else None,
        "drawdownTradingDaysHeld": (
            evaluation.get("drawdownTradingDaysHeld") if evaluation else None
        ),
        "drawdownCalendarDaysHeld": (
            evaluation.get("drawdownCalendarDaysHeld") if evaluation else None
        ),
        "tradingDaysToMinAfter": (
            evaluation.get("tradingDaysToMinAfter") if evaluation else None
        ),
        "calendarDaysToMinAfter": (
            evaluation.get("calendarDaysToMinAfter") if evaluation else None
        ),
    }


def choose_batch_analysis(
    analyses: list[tuple[str, dict]]
) -> tuple[str, dict]:
    detected = [(mode, analysis) for mode, analysis in analyses if analysis.get("detected")]
    if not detected:
        return analyses[0]

    def sort_key(item: tuple[str, dict]) -> tuple[str, int]:
        mode, analysis = item
        evaluation = primary_bottom_evaluation(analysis)
        date_text = (
            evaluation.get("date") if evaluation else analysis.get("stableDate")
        ) or ""
        return date_text, 1 if mode == "general" else 0

    return max(detected, key=sort_key)


def normalize_batch_mode(value: str | None) -> str:
    normalized = (value or "general").strip().lower()
    if normalized not in {"general", "ipo", "both"}:
        raise ValueError("まとめて分析モードは general / ipo / both のどれかを指定してください。")
    return normalized


def analyze_one_for_batch(
    raw_symbol: str,
    mode: str = "general",
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
    disable_saved_analysis_reuse: bool = False,
) -> dict:
    return analyze_one_for_batch_with_update(
        raw_symbol,
        mode,
        update_missing=True,
        delayed_buy_days=delayed_buy_days,
        delayed_buy_enabled=delayed_buy_enabled,
        drawdown_buy_percent=drawdown_buy_percent,
        drawdown_buy_enabled=drawdown_buy_enabled,
        drawdown_miss_zero_enabled=drawdown_miss_zero_enabled,
        disable_saved_analysis_reuse=disable_saved_analysis_reuse,
    )


def analyze_one_for_batch_with_update(
    raw_symbol: str,
    mode: str = "general",
    update_missing: bool = True,
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
    disable_saved_analysis_reuse: bool = False,
) -> dict:
    mode = normalize_batch_mode(mode)
    delayed_buy_days = normalize_delayed_buy_days(delayed_buy_days)
    drawdown_buy_percent = normalize_drawdown_buy_percent(drawdown_buy_percent)
    parts = [part.strip() for part in raw_symbol.split("|", 1)]
    security_type = (
        normalize_security_type(parts[1]) if len(parts) == 2 else "stock"
    )
    symbol = normalize_symbol(parts[0], "auto")
    with batch_timing_step("保存済みキャッシュ確認"):
        cached = cached_stock_result(symbol)
    metadata = None
    if not cached:
        with batch_timing_step("初期メタデータ取得"):
            metadata = fetch_stock_data(symbol, "1mo")
    with batch_timing_step("価格データ更新・底練り判定"):
        history, analysis, _changed = ensure_symbol_cache(
            symbol,
            metadata=metadata,
            update_missing=update_missing,
            security_type=security_type,
            history_scope="long" if mode in {"general", "both"} else "ipo",
            prefer_saved_analysis=not disable_saved_analysis_reuse,
        )
    if mode == "general":
        selected_mode, selected_analysis = "general", analysis
    elif mode == "ipo":
        selected_mode = "ipo"
        with batch_timing_step("上場後特化モード再判定"):
            selected_analysis = analyze_bottoming(
                history.points,
                security_type=history.security_type,
                mode="ipo",
            )
    else:
        with batch_timing_step("上場後特化モード再判定"):
            ipo_analysis = analyze_bottoming(
                history.points,
                security_type=history.security_type,
                mode="ipo",
            )
        with batch_timing_step("採用モード選択"):
            selected_mode, selected_analysis = choose_batch_analysis(
                [("general", analysis), ("ipo", ipo_analysis)]
            )
    with batch_timing_step("まとめて表示用指標作成"):
        return batch_result_from_analysis(
            raw_symbol,
            history,
            selected_analysis,
            selected_mode,
            delayed_buy_days,
            delayed_buy_enabled,
            drawdown_buy_percent,
            drawdown_buy_enabled,
            drawdown_miss_zero_enabled,
        )


def parse_batch_symbols(raw_text: str) -> list[str]:
    raw_symbols = [
        item for item in re.split(r"[\s,;、]+", raw_text) if item.strip()
    ]
    return list(dict.fromkeys(raw_symbols))


def all_known_batch_symbols() -> list[str]:
    candidates: list[str] = [item["symbol"] for item in SYMBOL_SEARCH_SEEDS]
    initialize_database()
    with database_connection() as connection:
        rows = connection.execute(
            "SELECT symbol FROM stocks ORDER BY symbol"
        ).fetchall()
    candidates.extend(row["symbol"] for row in rows)
    return list(dict.fromkeys(candidates))


def batch_universe_symbols(universe: str | None = None) -> list[str]:
    normalized = (universe or "known").strip().lower()
    known = all_known_batch_symbols()
    if normalized in {"", "known", "saved"}:
        return known
    if normalized == "saved_only":
        initialize_database()
        with database_connection() as connection:
            rows = connection.execute(
                "SELECT symbol FROM stocks ORDER BY symbol"
            ).fetchall()
        return list(dict.fromkeys(row["symbol"] for row in rows))
    if normalized == "manual":
        return []
    selected = BATCH_UNIVERSES.get(normalized)
    if selected is None:
        selected = BATCH_UNIVERSES["all_core"]
    if normalized == "all_core":
        return list(dict.fromkeys(known + selected))
    return list(dict.fromkeys(selected))


def batch_symbol_for_market_cap(raw_symbol: str) -> tuple[str, str]:
    parts = [part.strip() for part in raw_symbol.split("|", 1)]
    symbol = normalize_symbol(parts[0], "auto")
    suffix = f"|{parts[1]}" if len(parts) == 2 and parts[1] else ""
    return f"{symbol}{suffix}", symbol


def market_cap_sorted_batch_symbols(
    raw_text: str,
    universe: str | None = None,
) -> list[str]:
    raw_symbols = parse_batch_symbols(raw_text)
    if not raw_symbols:
        raw_symbols = batch_universe_symbols(universe)
    normalized_pairs: list[tuple[str, str]] = []
    for raw_symbol in raw_symbols:
        try:
            normalized_pairs.append(batch_symbol_for_market_cap(raw_symbol))
        except Exception:
            normalized_pairs.append((raw_symbol, raw_symbol))
    deduped_pairs: list[tuple[str, str]] = []
    seen_symbols: set[str] = set()
    for raw, symbol in normalized_pairs:
        key = symbol.strip().upper()
        if key in seen_symbols:
            continue
        seen_symbols.add(key)
        deduped_pairs.append((raw, symbol))
    normalized_pairs = deduped_pairs
    quote_symbols = [symbol for _raw, symbol in normalized_pairs]
    market_caps = fetch_market_caps(quote_symbols)
    indexed = list(enumerate(normalized_pairs))
    indexed.sort(
        key=lambda item: (
            market_caps.get(item[1][1]) is not None,
            market_caps.get(item[1][1]) or 0,
            -item[0],
        ),
        reverse=True,
    )
    return [raw for _index, (raw, _symbol) in indexed]


def market_cap_sorted_batch_symbols_with_warning(
    raw_text: str,
    universe: str | None = None,
) -> tuple[list[str], str | None]:
    raw_symbols = parse_batch_symbols(raw_text)
    if not raw_symbols:
        raw_symbols = batch_universe_symbols(universe)
    try:
        return market_cap_sorted_batch_symbols(raw_text, universe), None
    except StockDataError as exc:
        return (
            raw_symbols,
            f"時価総額の取得に失敗したため、入力順/既知順で分析します（分類: {exc.category}）。",
        )


def batch_job_public_state(job: dict) -> dict:
    results = [item for item in job["results"] if item is not None]
    return {
        "jobId": job["id"],
        "status": job["status"],
        "total": job["total"],
        "completed": job["completed"],
        "current": job.get("current"),
        "startedAt": job["startedAt"],
        "finishedAt": job.get("finishedAt"),
        "cancelRequested": job.get("cancelRequested", False),
        "mode": job.get("mode", "general"),
        "universe": job.get("universe", "manual"),
        "delayedBuyDays": job.get("delayedBuyDays", DEFAULT_DELAYED_BUY_DAYS),
        "delayedBuyEnabled": job.get("delayedBuyEnabled", True),
        "drawdownBuyPercent": job.get(
            "drawdownBuyPercent", DEFAULT_DRAWDOWN_BUY_PERCENT
        ),
        "drawdownBuyEnabled": job.get("drawdownBuyEnabled", True),
        "drawdownMissZeroEnabled": job.get("drawdownMissZeroEnabled", False),
        "disableSavedAnalysisReuse": job.get("disableSavedAnalysisReuse", False),
        "runUntilLimit": job.get("runUntilLimit", False),
        "stopReason": job.get("stopReason"),
        "warning": job.get("warning"),
        "results": results,
        "errors": job["errors"],
        "timingRanking": aggregate_batch_timings(results),
        "slowestSymbols": slowest_batch_symbols(results),
    }


def get_batch_job(job_id: str) -> dict:
    with BATCH_JOBS_LOCK:
        job = BATCH_JOBS.get(job_id)
        if not job:
            raise ValueError("まとめて分析ジョブが見つかりません。")
        return batch_job_public_state(job)


def request_batch_cancel(job_id: str) -> dict:
    with BATCH_JOBS_LOCK:
        job = BATCH_JOBS.get(job_id)
        if not job:
            raise ValueError("まとめて分析ジョブが見つかりません。")
        if job["status"] == "running":
            job["cancelRequested"] = True
            job["status"] = "canceling"
        return batch_job_public_state(job)


def run_batch_job(job_id: str) -> None:
    while True:
        with BATCH_JOBS_LOCK:
            job = BATCH_JOBS.get(job_id)
            if not job:
                return
            if job.get("cancelRequested"):
                job["status"] = "canceled"
                job["finishedAt"] = utc_now_text()
                return
            next_index = None
            for index, item in enumerate(job["symbols"]):
                if job["results"][index] is None:
                    next_index = index
                    symbol_text = item
                    break
            if next_index is None:
                job["status"] = "completed"
                job["finishedAt"] = utc_now_text()
                return
            job["status"] = "running"
            job["current"] = symbol_text
            mode = job.get("mode", "general")
            delayed_buy_days = job.get("delayedBuyDays", DEFAULT_DELAYED_BUY_DAYS)
            delayed_buy_enabled = job.get("delayedBuyEnabled", True)
            drawdown_buy_percent = job.get(
                "drawdownBuyPercent", DEFAULT_DRAWDOWN_BUY_PERCENT
            )
            drawdown_buy_enabled = job.get("drawdownBuyEnabled", True)
            drawdown_miss_zero_enabled = job.get("drawdownMissZeroEnabled", False)
            disable_saved_analysis_reuse = job.get("disableSavedAnalysisReuse", False)

        timings: dict = {}
        timing_token = CURRENT_BATCH_TIMINGS.set(timings)
        symbol_started = time.perf_counter()
        stop_after_rate_limit = False
        try:
            result = analyze_one_for_batch(
                symbol_text,
                mode,
                delayed_buy_days,
                delayed_buy_enabled,
                drawdown_buy_percent,
                drawdown_buy_enabled,
                drawdown_miss_zero_enabled,
                disable_saved_analysis_reuse,
            )
        except StockDataError as exc:
            result = {
                "input": symbol_text,
                "error": f"{exc}（分類: {exc.category}）",
                "errorCategory": exc.category,
                "detected": False,
            }
            if job.get("runUntilLimit") and exc.category == "rate_limit":
                stop_after_rate_limit = True
        except Exception as exc:
            result = {
                "input": symbol_text,
                "error": str(exc),
                "errorCategory": "unknown",
                "detected": False,
            }
        finally:
            CURRENT_BATCH_TIMINGS.reset(timing_token)
        result["elapsedSeconds"] = round(time.perf_counter() - symbol_started, 3)
        result["timings"] = normalized_timing_items(timings)

        with BATCH_JOBS_LOCK:
            job = BATCH_JOBS.get(job_id)
            if not job:
                return
            if job["results"][next_index] is None:
                job["results"][next_index] = result
                job["completed"] = sum(
                    1 for item in job["results"] if item is not None
                )
                if result.get("error"):
                    job["errors"].append(result)
            if stop_after_rate_limit:
                job["status"] = "canceled"
                job["stopReason"] = "rate_limit"
                job["finishedAt"] = utc_now_text()
                return


def start_batch_job(
    raw_text: str,
    mode: str = "general",
    sort_by_market_cap: bool = False,
    run_until_limit: bool = False,
    universe: str | None = None,
    delayed_buy_days: int = DEFAULT_DELAYED_BUY_DAYS,
    delayed_buy_enabled: bool = True,
    drawdown_buy_percent: float = DEFAULT_DRAWDOWN_BUY_PERCENT,
    drawdown_buy_enabled: bool = True,
    drawdown_miss_zero_enabled: bool = False,
    disable_saved_analysis_reuse: bool = False,
) -> dict:
    mode = normalize_batch_mode(mode)
    delayed_buy_days = normalize_delayed_buy_days(delayed_buy_days)
    drawdown_buy_percent = normalize_drawdown_buy_percent(drawdown_buy_percent)
    warning = None
    if sort_by_market_cap:
        unique_symbols, warning = market_cap_sorted_batch_symbols_with_warning(
            raw_text,
            universe,
        )
    else:
        unique_symbols = parse_batch_symbols(raw_text)
        if not unique_symbols and universe and universe != "manual":
            unique_symbols = batch_universe_symbols(universe)
    if not unique_symbols:
        raise ValueError("銘柄コードを入力してください。")
    job_id = uuid.uuid4().hex
    now = utc_now_text()
    job = {
        "id": job_id,
        "status": "queued",
        "symbols": unique_symbols,
        "total": len(unique_symbols),
        "completed": 0,
        "current": None,
        "results": [None] * len(unique_symbols),
        "errors": [],
        "cancelRequested": False,
        "mode": mode,
        "universe": universe or "manual",
        "delayedBuyDays": delayed_buy_days,
        "delayedBuyEnabled": delayed_buy_enabled,
        "drawdownBuyPercent": drawdown_buy_percent,
        "drawdownBuyEnabled": drawdown_buy_enabled,
        "drawdownMissZeroEnabled": drawdown_miss_zero_enabled,
        "disableSavedAnalysisReuse": disable_saved_analysis_reuse,
        "runUntilLimit": run_until_limit,
        "stopReason": None,
        "warning": warning,
        "startedAt": now,
        "finishedAt": None,
    }
    with BATCH_JOBS_LOCK:
        BATCH_JOBS[job_id] = job
    threading.Thread(target=run_batch_job, args=(job_id,), daemon=True).start()
    return batch_job_public_state(job)


HTML_PAGE = r"""<!doctype html>
<html lang="ja">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>世界の株価・底練り判定</title>
  <style>
    :root {
      --bg:#eef3f8; --panel:#fff; --text:#172033; --muted:#64748b;
      --blue:#2563eb; --blue2:#60a5fa; --green:#059669; --green2:#d1fae5;
      --red:#dc2626; --amber:#d97706; --purple:#7c3aed; --line:#dce3ec;
      --shadow:0 10px 28px rgba(15,23,42,.07);
    }
    * { box-sizing:border-box; }
    body {
      margin:0; min-width:780px; color:var(--text); background:var(--bg);
      font-family:"Yu Gothic UI","Meiryo",system-ui,sans-serif;
    }
    .app { max-width:1240px; margin:0 auto; padding:30px; }
    h1 { margin:0; font-size:28px; }
    h2 { margin:0 0 6px; font-size:21px; }
    h3 { margin:0; font-size:16px; }
    .subtitle,.note { color:var(--muted); }
    .subtitle { margin:6px 0 20px; font-size:14px; }
    .note { font-size:12px; line-height:1.7; }
    .panel {
      background:var(--panel); border:1px solid rgba(148,163,184,.17);
      border-radius:16px; box-shadow:var(--shadow);
    }
    .search-panel {
      display:grid; grid-template-columns:2fr 1.25fr 1fr 1fr 1.45fr auto;
      gap:14px; align-items:end; padding:18px;
    }
    .range-panel {
      display:grid; grid-template-columns:1.2fr repeat(4,1fr) auto;
      gap:14px; align-items:end; padding:14px 18px; margin-top:-8px;
    }
    label { display:block; margin-bottom:6px; color:#475569; font-size:13px; font-weight:700; }
    input,select,textarea,button { border-radius:9px; font:inherit; outline:none; }
    input,select,textarea {
      width:100%; padding:0 12px; color:var(--text); background:#fff;
      border:1px solid #cbd5e1;
    }
    input,select { height:43px; }
    textarea { min-height:105px; padding:10px 12px; resize:vertical; line-height:1.6; }
    .simulation-toggle {
      display:flex; align-items:center; gap:7px; margin:0 0 6px;
      color:#475569; font-size:13px; font-weight:700;
    }
    .simulation-toggle input { width:auto; height:auto; }
    input:focus,select:focus,textarea:focus {
      border-color:var(--blue); box-shadow:0 0 0 3px rgba(37,99,235,.12);
    }
    button {
      height:43px; padding:0 20px; cursor:pointer; border:0; font-weight:700;
      transition:.15s ease;
    }
    button:hover { transform:translateY(-1px); }
    button:disabled { cursor:wait; opacity:.6; transform:none; }
    .primary { min-width:132px; color:#fff; background:var(--blue); }
    .secondary { color:#fff; background:#334155; }
    .examples {
      display:flex; align-items:center; flex-wrap:wrap; gap:8px;
      margin:12px 4px 18px; color:var(--muted); font-size:12px;
    }
    .symbol-search {
      position:relative; display:flex; gap:8px; align-items:center;
      margin:0 4px 16px;
    }
    .symbol-search input { max-width:340px; }
    .event-controls {
      display:flex; align-items:center; flex-wrap:wrap; gap:10px;
      margin:0 4px 16px; padding:10px 12px; border:1px solid #dbe4ef;
      border-radius:12px; background:#f8fafc;
    }
    .event-controls .simulation-toggle { margin:0; }
    .event-controls .note { margin-left:2px; }
    .top-run-status {
      display:flex; align-items:center; justify-content:space-between; gap:12px;
      margin:0 4px 16px; padding:11px 13px; border:1px solid #dbe4ef;
      border-radius:12px; background:#fff; box-shadow:0 4px 14px rgba(15,23,42,.04);
    }
    .top-run-message { color:#334155; font-size:13px; font-weight:700; }
    .top-progresses { display:flex; flex-wrap:wrap; justify-content:flex-end; gap:12px; }
    .search-results {
      position:absolute; z-index:20; top:42px; left:0; width:min(520px,100%);
      max-height:260px; overflow:auto; border:1px solid #dbe4ef;
      border-radius:12px; background:#fff; box-shadow:var(--shadow);
    }
    .search-result {
      display:flex; justify-content:space-between; gap:10px; width:100%;
      padding:10px 12px; border:0; border-bottom:1px solid #edf2f7;
      color:#172033; background:#fff; text-align:left; cursor:pointer;
    }
    .search-result:hover { background:#f8fafc; }
    .search-result small { color:#64748b; }
    .chip { height:29px; padding:0 11px; color:#475569; background:#e2e8f0; font-size:12px; }
    .info-panel { margin-bottom:16px; padding:18px 20px; }
    .company { min-height:27px; margin-bottom:15px; font-size:18px; font-weight:800; }
    .metrics { display:grid; grid-template-columns:repeat(4,1fr); gap:15px; }
    .metric { min-width:0; padding-right:15px; border-right:1px solid #e2e8f0; }
    .metric:last-child { border:0; }
    .metric-name { color:var(--muted); font-size:12px; }
    .metric-value { margin-top:4px; font-size:20px; line-height:1.25; font-weight:800; }
    .metric-date { margin-top:3px; color:var(--muted); font-size:11px; }
    .chart-panel { height:420px; margin-bottom:16px; padding:14px; }
    canvas { display:block; width:100%; height:100%; }
    .section-panel { margin-top:18px; padding:20px; }
    .section-head {
      display:flex; justify-content:space-between; gap:20px; align-items:flex-start;
      margin-bottom:16px;
    }
    .badge {
      display:inline-flex; align-items:center; min-height:32px; padding:6px 12px;
      border-radius:999px; font-size:13px; font-weight:800;
    }
    .badge.detected { color:#047857; background:#d1fae5; }
    .badge.waiting { color:#92400e; background:#fef3c7; }
    .stability-summary {
      display:grid; grid-template-columns:1.2fr repeat(4,1fr); gap:12px; margin-bottom:15px;
    }
    .summary-card { padding:14px; border:1px solid #e2e8f0; border-radius:12px; background:#f8fafc; }
    .summary-card .big { margin-top:5px; font-size:21px; font-weight:800; }
    .score-card { position:relative; overflow:hidden; }
    .score-track { height:7px; margin-top:10px; overflow:hidden; border-radius:99px; background:#e2e8f0; }
    .score-fill { height:100%; border-radius:99px; }
    .analysis-chart { height:500px; padding:8px 0 0; }
    .candidate-panel {
      display:grid; grid-template-columns:260px 1fr; gap:12px;
      margin:14px 0; padding:13px; border:1px solid #e2e8f0;
      border-radius:12px; background:#f8fafc;
    }
    .candidate-panel select { width:100%; }
    .candidate-detail { color:#334155; font-size:13px; line-height:1.65; }
    .chart-tooltip {
      position:fixed; z-index:50; pointer-events:none; min-width:190px;
      padding:9px 10px; border:1px solid #dbe4ef; border-radius:10px;
      background:rgba(255,255,255,.96); box-shadow:var(--shadow);
      color:#172033; font-size:12px; line-height:1.5;
    }
    .algorithm {
      display:grid; grid-template-columns:repeat(4,1fr); gap:12px; margin-top:15px;
    }
    .algorithm div { padding:13px; border-radius:11px; background:#f8fafc; border:1px solid #e2e8f0; }
    .algorithm strong { display:block; margin-bottom:5px; font-size:13px; }
    .cache-stats {
      display:grid; grid-template-columns:repeat(4,1fr); gap:12px; margin:14px 0;
    }
    .cache-stat {
      padding:13px; border:1px solid #e2e8f0; border-radius:11px; background:#f8fafc;
    }
    .cache-stat strong { display:block; margin-top:4px; font-size:20px; }
    .cache-actions { display:flex; flex-wrap:wrap; gap:10px; }
    .cache-actions button { min-width:150px; }
    .cache-message { margin:12px 0 0; color:var(--muted); font-size:12px; }
    .batch-grid { display:grid; grid-template-columns:330px 1fr; gap:18px; align-items:start; }
    .batch-actions { display:flex; gap:10px; margin-top:10px; }
    .column-picker {
      margin-top:14px; padding:12px; border:1px solid var(--line); border-radius:12px;
      background:#f8fafc;
    }
    .column-picker-title {
      display:flex; justify-content:space-between; align-items:center; gap:10px;
      color:#475569; font-size:12px; font-weight:700; margin-bottom:8px;
    }
    .column-picker-actions { display:flex; gap:8px; }
    .mini-button {
      border:1px solid var(--line); background:#fff; color:#334155; border-radius:999px;
      padding:4px 9px; font-size:11px; cursor:pointer;
    }
    .column-options { display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:10px; }
    .column-group {
      padding:8px; border:1px solid #e2e8f0; border-radius:10px; background:#fff;
    }
    .column-group-title {
      margin:0 0 7px; color:#64748b; font-size:11px; font-weight:800;
    }
    .column-group-items { display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:6px; }
    .column-options label {
      display:flex; align-items:center; gap:5px; min-height:26px;
      padding:3px 5px; border-radius:7px; font-size:12px; color:#334155;
      user-select:none;
    }
    .column-options label:hover { background:#f1f5f9; }
    .histogram { height:420px; padding:6px 0; }
    .contribution-panel {
      margin-top:12px; display:grid; grid-template-columns:260px 1fr; gap:14px;
      align-items:start; padding:12px; border:1px solid var(--line);
      border-radius:14px; background:#f8fafc;
    }
    .contribution-panel.hidden { display:none; }
    .contribution-chart { height:250px; }
    .contribution-list { max-height:260px; overflow:auto; font-size:12px; color:#334155; }
    .contribution-row {
      display:grid; grid-template-columns:34px 88px 1fr 74px 66px; gap:8px;
      padding:6px 0; border-bottom:1px solid #e2e8f0; align-items:center;
    }
    .contribution-row.header { font-weight:700; color:#475569; }
    .timing-panel {
      margin-top:10px; padding:10px; border:1px solid var(--line);
      border-radius:12px; background:#fff; color:#334155; font-size:12px;
    }
    .timing-panel.hidden { display:none; }
    .timing-grid { display:grid; grid-template-columns:1fr 1fr; gap:12px; }
    .timing-title { margin-bottom:6px; color:#475569; font-weight:800; }
    .timing-row {
      display:grid; grid-template-columns:1fr 66px 54px 58px; gap:8px;
      padding:4px 0; border-bottom:1px solid #eef2f7; align-items:center;
    }
    .timing-row.symbol { grid-template-columns:82px 1fr 66px; }
    .timing-row.header { color:#64748b; font-weight:800; }
    .table-wrap { margin-top:16px; overflow:auto; }
    table { width:100%; border-collapse:collapse; font-size:13px; }
    th,td { padding:9px 10px; border-bottom:1px solid #e2e8f0; text-align:left; white-space:nowrap; }
    th { color:#475569; background:#f8fafc; }
    .status-row {
      display:flex; justify-content:space-between; align-items:center; margin-top:12px;
    }
    .status { min-height:20px; color:var(--muted); font-size:13px; }
    .search-progress {
      display:inline-flex; align-items:center; gap:7px; margin-left:10px;
      vertical-align:middle; color:#475569; font-size:12px;
    }
    .progress-track {
      width:96px; height:6px; overflow:hidden; border-radius:999px; background:#dbe4ef;
    }
    .progress-fill {
      width:0%; height:100%; border-radius:999px;
      background:linear-gradient(90deg,#2563eb,#60a5fa);
      transition:width .18s ease;
    }
    .spinner {
      display:none; width:16px; height:16px; margin-right:8px; vertical-align:-3px;
      border:2px solid #bfdbfe; border-top-color:var(--blue); border-radius:50%;
      animation:spin .7s linear infinite;
    }
    .loading .spinner { display:inline-block; }
    .quit { height:32px; padding:0 12px; color:#64748b; background:transparent; font-size:12px; }
    .error { color:var(--red); }
    .hidden { display:none; }
    @keyframes spin { to { transform:rotate(360deg); } }
    @media (max-width:950px) {
      .app { padding:20px; }
      .search-panel { grid-template-columns:1.5fr 1fr 1fr 1fr; }
      .search-panel .action { grid-column:1/-1; }
      .range-panel { grid-template-columns:1fr 1fr; }
      .range-panel .action { grid-column:1/-1; }
      .primary { width:100%; }
      .stability-summary { grid-template-columns:repeat(2,1fr); }
      .candidate-panel { grid-template-columns:1fr; }
      .algorithm { grid-template-columns:repeat(2,1fr); }
      .cache-stats { grid-template-columns:repeat(2,1fr); }
      .batch-grid { grid-template-columns:1fr; }
    }
  </style>
</head>
<body>
<main class="app">
  <h1>世界の株価・底練り判定</h1>
  <p class="subtitle">大きく売られた後に、値動きが落ち着き、底が固まりつつあるかを確認します。買い時の断定ではなく、底打ち候補の発見を目的にします。</p>

  <section class="panel search-panel">
    <div>
      <label for="symbol">銘柄コード</label>
      <input id="symbol" value="7203" autocomplete="off" placeholder="例：7203 / AAPL">
    </div>
    <div>
      <label for="market">市場</label>
      <select id="market">
        <option value="auto">自動判定</option>
        <option value="japan">日本（東京）</option>
        <option value="usa">米国</option>
        <option value="uk">英国（ロンドン）</option>
        <option value="germany">ドイツ</option>
        <option value="hongkong">香港</option>
      </select>
    </div>
    <div>
      <label for="period">通常チャート期間</label>
      <select id="period">
        <option value="1mo">1か月</option>
        <option value="3mo">3か月</option>
        <option value="6mo">6か月</option>
        <option value="1y" selected>1年</option>
        <option value="5y">5年</option>
        <option value="max">全期間</option>
      </select>
    </div>
    <div>
      <label for="securityType">商品区分</label>
      <select id="securityType">
        <option value="stock" selected>株式</option>
        <option value="etf">ETF</option>
      </select>
    </div>
    <div>
      <label for="algorithmMode">判定モード</label>
      <select id="algorithmMode">
        <option value="general" selected>汎用：大調整後</option>
        <option value="ipo">上場後特化</option>
      </select>
    </div>
    <div class="action"><button id="search" class="primary">検索・分析</button></div>
  </section>

  <section class="panel range-panel">
    <div>
      <label>底練りの分析範囲</label>
      <div class="note">空欄なら通常どおり全履歴で判定。任意の日付を入れると、その範囲内だけで底練り状態を再判定します。</div>
    </div>
    <div>
      <label for="analysisStart">分析開始日</label>
      <input id="analysisStart" type="text" inputmode="numeric" maxlength="10" placeholder="YYYY-MM-DD">
    </div>
    <div>
      <label for="analysisEnd">分析終了日</label>
      <input id="analysisEnd" type="text" inputmode="numeric" maxlength="10" placeholder="YYYY-MM-DD">
    </div>
    <div>
      <label class="simulation-toggle"><input id="enableDelayedBuy" type="checkbox" checked>遅延買付</label>
      <input id="delayedBuyDays" type="number" min="0" max="5000" step="1" value="106" title="底検知から何営業日後に買うか">
    </div>
    <div>
      <label class="simulation-toggle"><input id="enableDrawdownBuy" type="checkbox" checked>下落待ち買付</label>
      <input id="drawdownBuyPercent" type="number" min="-99" max="0" step="0.1" value="-20" title="底検知価格から何％下げたら買うか">
      <label class="simulation-toggle"><input id="drawdownMissZero" type="checkbox">下落待ち未約定を0%扱い</label>
    </div>
    <div class="action"><button id="clearAnalysisRange" class="secondary" type="button">範囲をクリア</button></div>
  </section>

  <div class="examples">
    <span>入力例：</span>
    <button class="chip" data-symbol="7203">トヨタ</button>
    <button class="chip" data-symbol="6758">ソニー</button>
    <button class="chip" data-symbol="AAPL">Apple</button>
    <button class="chip" data-symbol="MSFT">Microsoft</button>
    <button class="chip" data-symbol="SAP.DE">SAP</button>
    <button class="chip" data-symbol="0700.HK">Tencent</button>
  </div>

  <div class="symbol-search">
    <input id="symbolSearch" autocomplete="off" placeholder="銘柄名・コード検索：例 半導体 / メルカリ / MSFT">
    <button id="symbolSearchButton" class="secondary" type="button">検索</button>
    <div id="symbolSearchResults" class="search-results hidden"></div>
  </div>

  <div class="event-controls">
    <label class="simulation-toggle">
      <input id="showImportantEvents" type="checkbox">
      重要開示日を表示
    </label>
    <button id="fetchImportantEvents" class="secondary" type="button" disabled>重要開示日を取得</button>
    <span id="importantEventStatus" class="note">初期状態では表示しません。必要な銘柄だけ取得してください。</span>
  </div>

  <div class="top-run-status">
    <div id="topRunStatus" class="top-run-message">銘柄を入力してください</div>
    <div class="top-progresses">
      <span id="topSearchProgress" class="search-progress hidden">
        <span class="progress-track"><span id="topSearchProgressFill" class="progress-fill"></span></span>
        <span id="topSearchProgressText">0%</span>
      </span>
      <span id="eventProgress" class="search-progress hidden">
        <span class="progress-track"><span id="eventProgressFill" class="progress-fill"></span></span>
        <span id="eventProgressText">0%</span>
      </span>
    </div>
  </div>

  <section class="panel info-panel">
    <div id="company" class="company">まだ銘柄が選択されていません</div>
    <div class="metrics">
      <div class="metric"><div class="metric-name">最新の終値</div><div id="latest" class="metric-value">—</div><div id="latestDate" class="metric-date"></div></div>
      <div class="metric"><div class="metric-name">期間内の最高値</div><div id="highest" class="metric-value">—</div><div id="highestDate" class="metric-date"></div></div>
      <div class="metric"><div class="metric-name">期間内の最安値</div><div id="lowest" class="metric-value">—</div><div id="lowestDate" class="metric-date"></div></div>
      <div class="metric"><div class="metric-name">期間騰落率</div><div id="change" class="metric-value">—</div><div class="metric-date">最初の終値との比較</div></div>
    </div>
  </section>

  <section class="panel chart-panel"><canvas id="priceChart"></canvas></section>

  <section id="stabilityPanel" class="panel section-panel hidden">
    <div class="section-head">
      <div>
        <h2>底練り・底打ち候補判定</h2>
        <div class="note">直近500営業日（履歴が短い銘柄は上場後データ）から、大幅調整、日柄、底練り、出来高付きブレイクを時系列順に検証します。</div>
      </div>
      <div id="stabilityBadge" class="badge waiting">分析前</div>
    </div>

    <div class="stability-summary">
      <div class="summary-card">
        <div class="metric-name">底打ち確認タイミング</div>
        <div id="stableDate" class="big">—</div>
        <div id="stableTiming" class="metric-date"></div>
      </div>
      <div class="summary-card score-card">
        <div class="metric-name">安値圏フィルター</div>
        <div id="priceLocationScore" class="big">—</div>
        <div class="score-track"><div id="priceLocationBar" class="score-fill" style="background:#dc2626;width:0"></div></div>
        <div id="priceLocationDetail" class="metric-date"></div>
      </div>
      <div class="summary-card score-card">
        <div class="metric-name">ボラティリティ縮小</div>
        <div id="volatilityScore" class="big">—</div>
        <div class="score-track"><div id="volatilityBar" class="score-fill" style="background:#2563eb;width:0"></div></div>
        <div id="volatilityDetail" class="metric-date"></div>
      </div>
      <div class="summary-card score-card">
        <div class="metric-name">60日終値レンジ</div>
        <div id="sidewaysScore" class="big">—</div>
        <div class="score-track"><div id="sidewaysBar" class="score-fill" style="background:#7c3aed;width:0"></div></div>
        <div id="sidewaysDetail" class="metric-date"></div>
      </div>
      <div class="summary-card score-card">
        <div class="metric-name">価格ブレイク確認</div>
        <div id="trendScore" class="big">—</div>
        <div class="score-track"><div id="trendBar" class="score-fill" style="background:#059669;width:0"></div></div>
        <div id="trendDetail" class="metric-date"></div>
      </div>
    </div>

    <div class="cache-stats">
      <div class="cache-stat"><span class="metric-name">過去の底打ち候補</span><strong id="backtestSignals">0回</strong></div>
      <div class="cache-stat"><span class="metric-name">5日後 平均 / 勝率</span><strong id="backtest5">—</strong></div>
      <div class="cache-stat"><span class="metric-name">20日後 平均 / 勝率</span><strong id="backtest20">—</strong></div>
      <div class="cache-stat"><span class="metric-name">60日後 平均 / 勝率</span><strong id="backtest60">—</strong></div>
    </div>

    <div id="bottomCandidatePanel" class="candidate-panel hidden">
      <div>
        <label for="bottomCandidateSelect">底打ち候補を選択</label>
        <select id="bottomCandidateSelect"></select>
      </div>
      <div id="bottomCandidateDetail" class="candidate-detail"></div>
    </div>

    <div class="analysis-chart"><canvas id="stabilityChart"></canvas></div>

    <div class="algorithm">
      <div><strong>1. 大調整と日柄（30点・必須）</strong><span class="note">過去500営業日の高値から株式は40%以上、ETFは25%以上下落し、さらに高値から一定日数が経過していることを確認します。</span></div>
      <div><strong>2. 値動きの縮小（20点・必須）</strong><span class="note">直近20営業日の平均絶対騰落率が2.5%以下で、ギャンブル的な値動きが収まっていることを確認します。</span></div>
      <div><strong>3. 底練り（25点・必須）</strong><span class="note">60営業日の終値レンジ20%以内を理想とし、ノイズの多いグロース株は30%まで許容します。</span></div>
      <div><strong>4. 価格ブレイク（25点・最終トリガー）</strong><span class="note">緑帯の後、60日高値の上抜け、または+5%以上・出来高2倍の上昇を探し、2営業日の維持を確認します。</span></div>
    </div>
    <p class="note">ゴールデンクロスは使わず、底練りが十分に続いた後の価格ブレイクと出来高急増、さらに2営業日のフォロースルーを確認します。将来データを見ない形で過去シグナルの5日後・20日後・60日後も集計します。</p>
  </section>

  <section class="panel section-panel">
    <div class="section-head">
      <div>
        <h2>保存データの管理</h2>
        <div class="note">一度取得した日足と判定結果をSQLiteへ保存します。確定済みの底打ち候補は通常更新を省略し、未確定銘柄だけ不足分を追加します。</div>
      </div>
      <div id="cacheVersion" class="badge waiting">保存準備中</div>
    </div>
    <div class="cache-stats">
      <div class="cache-stat"><span class="metric-name">保存銘柄</span><strong id="cacheStockCount">0社</strong></div>
      <div class="cache-stat"><span class="metric-name">保存日足</span><strong id="cachePriceCount">0件</strong></div>
      <div class="cache-stat"><span class="metric-name">分析済み</span><strong id="cacheAnalysisCount">0社</strong></div>
      <div class="cache-stat"><span class="metric-name">底打ち候補検出</span><strong id="cacheDetectedCount">0社</strong></div>
    </div>
    <div class="cache-actions">
      <button id="cacheUpdate" class="primary">最新データを追加</button>
      <button id="cacheAnalyzeMissing" class="secondary">未分析銘柄を分析</button>
      <button id="cacheReanalyze" class="secondary">全結果を再計算</button>
      <button id="cacheShow" class="secondary">保存結果を表示</button>
      <button id="marketCapCsvImport" class="secondary" type="button">時価総額CSV読込</button>
      <input id="marketCapCsvFile" type="file" accept=".csv,text/csv" class="hidden">
    </div>
    <p id="cacheMessage" class="cache-message">検索または一括分析した銘柄は自動的に保存されます。</p>
  </section>

  <section class="panel section-panel">
    <div class="section-head">
      <div>
        <h2>複数銘柄の安定タイミング集計</h2>
        <div class="note">最大15銘柄。改行、空白、またはカンマで区切って入力してください。</div>
      </div>
    </div>
    <div class="batch-grid">
      <div>
        <label for="batchSymbols">銘柄コード一覧</label>
        <textarea id="batchSymbols" placeholder="例：&#10;7203&#10;6758&#10;AAPL&#10;VOO|ETF">7203
6758
AAPL
VOO|ETF</textarea>
        <label for="batchMode">まとめて分析モード</label>
        <select id="batchMode">
          <option value="general" selected>汎用：大調整後の底練り</option>
          <option value="ipo">上場後特化：IPO後の暴騰暴落</option>
          <option value="both">両方：検出した最新候補を採用</option>
        </select>
        <label for="batchUniverse">分析対象ユニバース</label>
        <select id="batchUniverse">
          <option value="manual" selected>入力欄の銘柄だけ</option>
          <option value="known">保存済み＋基本候補</option>
          <option value="saved_only">保存済みだけ</option>
          <option value="japan_large">日本株大型候補</option>
          <option value="us_large">米国大型候補</option>
          <option value="semiconductor">半導体関連候補</option>
          <option value="tse_growth">東証グロース候補</option>
          <option value="nasdaq100">NASDAQ100候補</option>
          <option value="sox_semiconductor">SOX/半導体拡張候補</option>
          <option value="etf_commodity">ETF・商品・指数候補</option>
          <option value="all_core">全部（保存済み＋主要ユニバース）</option>
        </select>
        <div class="batch-actions">
          <button id="batchAnalyze" class="secondary">まとめて分析</button>
          <button id="batchMarketCapAnalyze" class="secondary" type="button">時価総額順で連続分析</button>
          <button id="batchCancel" class="secondary" type="button" disabled>中断</button>
          <button id="batchCsv" class="secondary" type="button" disabled>CSV出力</button>
        </div>
        <label class="simulation-toggle" title="新しい出力項目を追加した直後など、保存済み分析を使わず全銘柄を再計算します。">
          <input id="disableSavedAnalysisReuse" type="checkbox">
          保存済み分析の再計算省略を使わない
        </label>
        <div class="column-picker">
          <div class="column-picker-title">
            <span>表示する列</span>
            <span class="column-picker-actions">
              <button id="batchColumnsBasic" class="mini-button" type="button">基本</button>
              <button id="batchColumnsAll" class="mini-button" type="button">全て</button>
            </span>
          </div>
          <div id="batchColumnOptions" class="column-options"></div>
        </div>
        <div class="column-picker">
          <div class="column-picker-title">
            <span>グラフ集計フィルター</span>
          </div>
          <label for="chartRecentYears">底検知日が直近N年以内</label>
          <input id="chartRecentYears" type="number" min="0" max="100" step="0.5" value="10" title="空欄にすると全期間を集計します">
          <p class="note">古すぎる勝ち組・生存者バイアスの影響を弱めるため、グラフだけを直近年数で絞ります。表とCSVは全件のままです。</p>
        </div>
        <p id="batchStatus" class="note">底打ち候補の確認までの日数を銘柄横断で集計します。</p>
        <div id="batchTimingPanel" class="timing-panel hidden"></div>
      </div>
      <div>
        <div class="histogram"><canvas id="histogramChart"></canvas></div>
        <div class="column-picker">
          <label class="simulation-toggle"><input id="showContributionBreakdown" type="checkbox">寄与額ランキングを表示</label>
          <label for="contributionTopN">上位N件</label>
          <input id="contributionTopN" type="number" min="1" max="50" step="1" value="10">
        </div>
        <div id="contributionPanel" class="contribution-panel hidden">
          <div class="contribution-chart"><canvas id="contributionChart"></canvas></div>
          <div id="contributionList" class="contribution-list"></div>
        </div>
      </div>
    </div>
    <div id="batchTableWrap" class="table-wrap hidden">
      <table>
        <thead id="batchTableHead"></thead>
        <tbody id="batchTableBody"></tbody>
      </table>
    </div>
  </section>

  <div class="status-row">
    <div id="status" class="status"><span class="spinner"></span><span id="statusText">銘柄を入力してください</span></div>
    <button id="quit" class="quit">アプリを終了</button>
  </div>
  <div id="searchProgress" class="search-progress hidden">
    <span class="progress-track"><span id="searchProgressFill" class="progress-fill"></span></span>
    <span id="searchProgressText">0%</span>
  </div>
</main>

<script>
  const $ = id => document.getElementById(id);
  let stockData = null;
  let showImportantEvents = false;
  let batchData = [];
  let currentBatchJobId = null;
  let batchPollTimer = null;
  const chartViews = {price:null, stability:null};
  const batchColumns = [
    {key:"symbol", label:"銘柄", basic:true, render:item => escapeHtml(item.symbol || item.input || "")},
    {key:"name", label:"名称", basic:true, render:item => escapeHtml(item.name || "")},
    {key:"algorithmMode", label:"採用モード", basic:true, render:item => item.algorithmMode === "ipo" ? "上場後特化" : "汎用"},
    {key:"listingDate", label:"上場日代理", basic:false, render:item => item.listingDate || "—"},
    {key:"stableDate", label:"底打ち候補日", basic:true, render:item => item.stableDate || "—"},
    {key:"stablePrice", label:"底打ち候補価格", basic:true, group:"価格・規模", render:item => item.stablePrice != null ? money(item.stablePrice, item.currency || "") : "—"},
    {key:"stablePriceJpy", label:"底打ち候補価格（円）", basic:true, group:"価格・規模", render:item => item.stablePriceJpy != null ? moneyJpy(item.stablePriceJpy) : "—"},
    {key:"estimatedMarketCapAtBottomJpy", label:"底検知時の推定時価総額", basic:true, group:"価格・規模", render:item => item.estimatedMarketCapAtBottomJpy != null ? moneyJpy(item.estimatedMarketCapAtBottomJpy) : "—"},
    {key:"currentMarketCapJpy", label:"現在の時価総額（円）", basic:false, group:"価格・規模", render:item => item.currentMarketCapJpy != null ? moneyJpy(item.currentMarketCapJpy) : "—"},
    {key:"calendarDaysToStable", label:"経過日数", basic:false, render:item => item.calendarDaysToStable != null ? item.calendarDaysToStable.toLocaleString()+"日" : "—"},
    {key:"previousPeak", label:"判定前最高値", basic:false, render:item => item.previousPeakDate ? `${item.previousPeakDate}<br><small>${money(item.previousPeakPrice, item.currency || "")}</small>` : "—"},
    {key:"drawdownFromPreviousPeakPercent", label:"高値からの下落率", basic:false, render:item => item.drawdownFromPreviousPeakPercent != null ? `${Number(item.drawdownFromPreviousPeakPercent).toFixed(2)}%` : "—"},
    {key:"bottomPositionRatio", label:"底位置指数", basic:true, render:item => item.bottomPositionRatio != null ? Number(item.bottomPositionRatio).toFixed(4) : "—"},
    {key:"maxBeforeActualBottom", label:"実底前の最高値", basic:false, render:item => item.maxBeforeActualBottomDate ? `${item.maxBeforeActualBottomDate}<br><small>${money(item.maxBeforeActualBottomPrice, item.currency || "")}</small>` : "—"},
    {key:"riseBeforeActualBottomPercent", label:"実底前上昇率", basic:false, render:item => item.riseBeforeActualBottomPercent != null ? `${Number(item.riseBeforeActualBottomPercent).toFixed(2)}%` : "—"},
    {key:"currentPrice", label:"現在価格", basic:false, render:item => item.currentDate ? `${item.currentDate}<br><small>${money(item.currentPrice, item.currency || "")}</small>` : "—"},
    {key:"holdingReturnPercent", label:"現在まで保有", basic:true, render:item => item.holdingReturnPercent != null ? `${Number(item.holdingReturnPercent).toFixed(2)}%` : "—"},
    {key:"immediateBuyRank", label:"底検知買い順位", basic:true, render:item => item.immediateBuyRank != null ? item.immediateBuyRank : "—"},
    {key:"annualizedReturnPercent", label:"年利換算", basic:true, render:item => item.annualizedReturnPercent != null ? `${Number(item.annualizedReturnPercent).toFixed(2)}%` : "—"},
    {key:"holdingDays", label:"保有期間", basic:false, render:item => item.tradingDaysHeld != null ? `${item.tradingDaysHeld.toLocaleString()}営業日` + (item.calendarDaysHeld != null ? `<br><small>${item.calendarDaysHeld.toLocaleString()}日</small>` : "") : "—"},
    {key:"delayedBuy", label:"遅延買付日", basic:false, render:item => item.delayedBuyDate ? `${item.delayedBuyDate}<br><small>${money(item.delayedBuyPrice, item.currency || "")}</small>` : "—"},
    {key:"delayedHoldingReturnPercent", label:"遅延買付リターン", basic:true, render:item => item.delayedHoldingReturnPercent != null ? `${Number(item.delayedHoldingReturnPercent).toFixed(2)}%` : "—"},
    {key:"delayedBuyRank", label:"遅延買い順位", basic:true, render:item => item.delayedBuyRank != null ? item.delayedBuyRank : "—"},
    {key:"delayedAnnualizedReturnPercent", label:"遅延買付年利", basic:true, render:item => item.delayedAnnualizedReturnPercent != null ? `${Number(item.delayedAnnualizedReturnPercent).toFixed(2)}%` : "—"},
    {key:"delayedHoldingDays", label:"遅延後保有期間", basic:false, render:item => item.delayedTradingDaysHeld != null ? `${item.delayedTradingDaysHeld.toLocaleString()}営業日` + (item.delayedCalendarDaysHeld != null ? `<br><small>${item.delayedCalendarDaysHeld.toLocaleString()}日</small>` : "") : "—"},
    {key:"drawdownBuy", label:"下落待ち買付日", basic:false, render:item => item.drawdownBuyDate ? `${item.drawdownBuyDate}<br><small>${money(item.drawdownBuyPrice, item.currency || "")}</small>` : "—"},
    {key:"drawdownHoldingReturnPercent", label:"下落待ちリターン", basic:true, render:item => item.drawdownHoldingReturnPercent != null ? `${Number(item.drawdownHoldingReturnPercent).toFixed(2)}%` : "—"},
    {key:"drawdownBuyRank", label:"下落待ち順位", basic:true, render:item => item.drawdownBuyRank != null ? item.drawdownBuyRank : "—"},
    {key:"drawdownAnnualizedReturnPercent", label:"下落待ち年利", basic:true, render:item => item.drawdownAnnualizedReturnPercent != null ? `${Number(item.drawdownAnnualizedReturnPercent).toFixed(2)}%` : "—"},
    {key:"drawdownHoldingDays", label:"下落待ち保有期間", basic:false, render:item => item.drawdownTradingDaysHeld != null ? `${item.drawdownTradingDaysHeld.toLocaleString()}営業日` + (item.drawdownCalendarDaysHeld != null ? `<br><small>${item.drawdownCalendarDaysHeld.toLocaleString()}日</small>` : "") : "—"},
    {key:"benchmarkHoldingReturnPercent", label:"オルカン相当リターン", basic:true, render:item => item.benchmarkHoldingReturnPercent != null ? `${Number(item.benchmarkHoldingReturnPercent).toFixed(2)}%` : "—"},
    {key:"benchmarkBuyRank", label:"オルカン相当順位", basic:true, render:item => item.benchmarkBuyRank != null ? item.benchmarkBuyRank : "—"},
    {key:"minAfter", label:"候補後の最安値", basic:false, render:item => item.minAfterDate ? `${item.minAfterDate}<br><small>${money(item.minAfterPrice, item.currency || "")}</small>` : "—"},
    {key:"drawdownAfterPercent", label:"候補後下落率", basic:true, render:item => item.drawdownAfterPercent != null ? `${Number(item.drawdownAfterPercent).toFixed(2)}%` : "—"},
    {key:"daysToMin", label:"実底まで", basic:false, render:item => {
      if (item.bottomVerdict !== "早すぎ" || item.tradingDaysToMinAfter == null) return "—";
      return `${item.tradingDaysToMinAfter.toLocaleString()}営業日後` +
        (item.calendarDaysToMinAfter != null ? `<br><small>${item.calendarDaysToMinAfter.toLocaleString()}日後</small>` : "");
    }},
    {key:"bottomVerdict", label:"成否", basic:true, render:item => {
      const color = item.bottomVerdict === "成功" ? "#059669" : item.bottomVerdict === "許容" ? "#d97706" : item.bottomVerdict === "早すぎ" ? "#dc2626" : "#64748b";
      return `<span style="color:${color}">${item.bottomVerdict || "—"}</span>`;
    }},
    {key:"detected", label:"判定", basic:true, render:item => `<span style="color:${item.detected ? "#059669" : "#d97706"}">${item.detected ? "検出" : "未検出"}</span>`}
  ];
  let visibleBatchColumns = new Set(batchColumns.filter(column => column.basic).map(column => column.key));

  function money(value, currency) {
    const digits = currency === "JPY" ? 0 : 2;
    const symbols = {JPY:"¥",USD:"$",EUR:"€",GBP:"£",HKD:"HK$"};
    const number = Number(value).toLocaleString("ja-JP", {
      minimumFractionDigits:digits, maximumFractionDigits:digits
    });
    return (symbols[currency] || "") + number + (symbols[currency] ? "" : " " + currency);
  }

  function moneyJpy(value) {
    if (value == null || !Number.isFinite(Number(value))) return "—";
    return "¥" + Math.round(Number(value)).toLocaleString("ja-JP");
  }

  function sanitizeDateInput(input) {
    let value = input.value.replace(/[^\d-]/g, "").slice(0, 10);
    const digits = value.replace(/\D/g, "");
    if (digits.length >= 8) {
      value = `${digits.slice(0,4)}-${digits.slice(4,6)}-${digits.slice(6,8)}`;
    }
    input.value = value;
  }

  function showTooltip(event, html) {
    let tooltip = $("chartTooltip");
    if (!tooltip) {
      tooltip = document.createElement("div");
      tooltip.id = "chartTooltip";
      tooltip.className = "chart-tooltip hidden";
      document.body.appendChild(tooltip);
    }
    tooltip.innerHTML = html;
    tooltip.classList.remove("hidden");
    const x = Math.min(event.clientX + 14, window.innerWidth - 230);
    const y = Math.min(event.clientY + 14, window.innerHeight - 150);
    tooltip.style.left = `${x}px`;
    tooltip.style.top = `${y}px`;
  }

  function hideTooltip() {
    const tooltip = $("chartTooltip");
    if (tooltip) tooltip.classList.add("hidden");
  }

  function nearestChartItem(view, event) {
    if (!view || !view.data.length) return null;
    const rect = view.canvas.getBoundingClientRect();
    const px = event.clientX - rect.left;
    const {left,right} = view.bounds;
    if (px < left || px > right) return null;
    const ratio = (px - left) / Math.max(1, right - left);
    const index = Math.max(0, Math.min(view.data.length - 1, Math.round(ratio * (view.data.length - 1))));
    return {item:view.data[index], index};
  }

  function updateBottomCandidates(data) {
    const panel = $("bottomCandidatePanel");
    const select = $("bottomCandidateSelect");
    const detail = $("bottomCandidateDetail");
    const items = data.bottomEvaluations || [];
    if (!items.length) {
      panel.classList.add("hidden");
      select.innerHTML = "";
      detail.textContent = "";
      return;
    }
    panel.classList.remove("hidden");
    select.innerHTML = items.map((item,index) =>
      `<option value="${index}">${item.index}. ${item.date} / ${money(item.price, stockData.currency)}</option>`
    ).join("");
    const render = () => {
      const item = items[Number(select.value || 0)];
      if (!item) return;
      const color = item.verdict === "成功" ? "#059669" : item.verdict === "許容" ? "#d97706" : "#dc2626";
      detail.innerHTML =
        `<strong>${item.date} の候補価格：</strong>${money(item.price, stockData.currency)}<br>` +
        `<strong>判定前最高値：</strong>${item.previousPeakDate || "—"} / ${item.previousPeakPrice == null ? "—" : money(item.previousPeakPrice, stockData.currency)} ` +
        `(${item.drawdownFromPreviousPeakPercent == null ? "—" : item.drawdownFromPreviousPeakPercent + "%"})<br>` +
        `<strong>底位置指数：</strong>${item.bottomPositionRatio == null ? "—" : item.bottomPositionRatio} ` +
        `<small>0に近いほど実底に近い判定</small><br>` +
        `<strong>実底前の最高値：</strong>${item.maxBeforeActualBottomDate || "—"} / ${item.maxBeforeActualBottomPrice == null ? "—" : money(item.maxBeforeActualBottomPrice, stockData.currency)} ` +
        `(${item.riseBeforeActualBottomPercent == null ? "—" : item.riseBeforeActualBottomPercent + "%"})<br>` +
        `<strong>現在価格：</strong>${item.currentDate || "—"} / ${item.currentPrice == null ? "—" : money(item.currentPrice, stockData.currency)}<br>` +
        `<strong>現在まで保有：</strong>${item.holdingReturnPercent == null ? "—" : item.holdingReturnPercent + "%"} ` +
        `（年利換算 ${item.annualizedReturnPercent == null ? "—" : item.annualizedReturnPercent + "%"} / ` +
        `${item.tradingDaysHeld == null ? "—" : item.tradingDaysHeld.toLocaleString() + "営業日"}）<br>` +
        `<strong>${item.delayedBuyDays ?? "—"}営業日後に買付：</strong>` +
        `${item.delayedBuyDate || "—"} / ${item.delayedBuyPrice == null ? "—" : money(item.delayedBuyPrice, stockData.currency)}<br>` +
        `<strong>遅延買付から現在まで：</strong>${item.delayedHoldingReturnPercent == null ? "—" : item.delayedHoldingReturnPercent + "%"} ` +
        `（年利換算 ${item.delayedAnnualizedReturnPercent == null ? "—" : item.delayedAnnualizedReturnPercent + "%"} / ` +
        `${item.delayedTradingDaysHeld == null ? "—" : item.delayedTradingDaysHeld.toLocaleString() + "営業日"}）<br>` +
        `<strong>${item.drawdownBuyPercent ?? "—"}%下落で買付：</strong>` +
        `${item.drawdownBuyDate || "—"} / ${item.drawdownBuyPrice == null ? "—" : money(item.drawdownBuyPrice, stockData.currency)} ` +
        `<small>目標 ${item.drawdownBuyTargetPrice == null ? "—" : money(item.drawdownBuyTargetPrice, stockData.currency)}</small><br>` +
        `<strong>下落待ち買付から現在まで：</strong>${item.drawdownHoldingReturnPercent == null ? "—" : item.drawdownHoldingReturnPercent + "%"} ` +
        `（年利換算 ${item.drawdownAnnualizedReturnPercent == null ? "—" : item.drawdownAnnualizedReturnPercent + "%"} / ` +
        `${item.drawdownTradingDaysHeld == null ? "—" : item.drawdownTradingDaysHeld.toLocaleString() + "営業日"}）<br>` +
        `<strong>その後の最安値：</strong>${item.minAfterDate} / ${money(item.minAfterPrice, stockData.currency)}<br>` +
        `<strong>候補日からの下落：</strong>${item.drawdownAfterPercent}%<br>` +
        `<strong style="color:${color}">判定：${item.verdict}</strong>　${item.verdictDetail}`;
    };
    select.onchange = render;
    render();
  }

  function setRunStatus(text) {
    $("statusText").textContent = text;
    if ($("topRunStatus")) $("topRunStatus").textContent = text;
  }

  function searchEstimateText() {
    const period = $("period")?.value || "1y";
    const hasCustomRange = Boolean(($("analysisStart")?.value || "").trim() || ($("analysisEnd")?.value || "").trim());
    if (hasCustomRange || period === "max" || period === "5y") return "目安：5〜30秒";
    return "目安：1〜10秒";
  }

  function importantEventEstimateText() {
    const symbol = stockData?.symbol || "";
    const isJapan = symbol.endsWith(".T") || /^[0-9A-Z]{4}\.T$/.test(symbol);
    if (isJapan) return "目安：10〜60秒（外部開示サイト確認）";
    return "目安：5〜30秒（外部開示サイト確認）";
  }

  function setLoading(active, text) {
    $("search").disabled = active;
    $("status").classList.toggle("loading", active);
    $("status").classList.remove("error");
    setRunStatus(text);
  }

  let searchProgressTimer = null;
  let searchProgressValue = 0;

  function setSearchProgress(value, label = "") {
    searchProgressValue = Math.max(0, Math.min(100, Math.round(value)));
    $("searchProgress").classList.remove("hidden");
    $("searchProgressFill").style.width = `${searchProgressValue}%`;
    $("searchProgressText").textContent = label
      ? `${searchProgressValue}% ${label}`
      : `${searchProgressValue}%`;
    if ($("topSearchProgress")) {
      $("topSearchProgress").classList.remove("hidden");
      $("topSearchProgressFill").style.width = `${searchProgressValue}%`;
      $("topSearchProgressText").textContent = label
        ? `${searchProgressValue}% ${label}`
        : `${searchProgressValue}%`;
    }
  }

  function startSearchProgress() {
    if (searchProgressTimer) clearInterval(searchProgressTimer);
    setSearchProgress(5, "開始");
    searchProgressTimer = setInterval(() => {
      const next = searchProgressValue < 55
        ? searchProgressValue + 4
        : searchProgressValue < 82
          ? searchProgressValue + 2
          : searchProgressValue < 94
            ? searchProgressValue + 1
            : searchProgressValue;
      setSearchProgress(next, next < 35 ? "取得中" : next < 75 ? "分析中" : "描画準備");
    }, 350);
  }

  function finishSearchProgress(success = true) {
    if (searchProgressTimer) {
      clearInterval(searchProgressTimer);
      searchProgressTimer = null;
    }
    setSearchProgress(success ? 100 : searchProgressValue, success ? "完了" : "停止");
    setTimeout(() => {
      if (!searchProgressTimer) $("searchProgress").classList.add("hidden");
      if (!searchProgressTimer && $("topSearchProgress")) $("topSearchProgress").classList.add("hidden");
    }, success ? 900 : 1600);
  }

  let eventProgressTimer = null;
  let eventProgressValue = 0;

  function setEventProgress(value, label = "") {
    eventProgressValue = Math.max(0, Math.min(100, Math.round(value)));
    $("eventProgress").classList.remove("hidden");
    $("eventProgressFill").style.width = `${eventProgressValue}%`;
    $("eventProgressText").textContent = label
      ? `${eventProgressValue}% ${label}`
      : `${eventProgressValue}%`;
  }

  function startEventProgress() {
    if (eventProgressTimer) clearInterval(eventProgressTimer);
    setEventProgress(4, "開示取得");
    eventProgressTimer = setInterval(() => {
      const next = eventProgressValue < 45
        ? eventProgressValue + 3
        : eventProgressValue < 78
          ? eventProgressValue + 2
          : eventProgressValue < 95
            ? eventProgressValue + 1
            : eventProgressValue;
      setEventProgress(next, next < 50 ? "外部確認" : next < 85 ? "保存中" : "描画準備");
    }, 420);
  }

  function finishEventProgress(success = true) {
    if (eventProgressTimer) {
      clearInterval(eventProgressTimer);
      eventProgressTimer = null;
    }
    setEventProgress(success ? 100 : eventProgressValue, success ? "完了" : "停止");
    setTimeout(() => {
      if (!eventProgressTimer) $("eventProgress").classList.add("hidden");
    }, success ? 1100 : 1800);
  }

  function showError(message) {
    $("status").classList.remove("loading");
    $("status").classList.add("error");
    setRunStatus(message);
    $("search").disabled = false;
  }

  function importantEventCount() {
    const events = [
      ...(stockData?.importantEvents || []),
      ...(stockData?.stability?.importantEvents || [])
    ];
    const seen = new Set();
    events.forEach(event => seen.add(`${event.eventDate}|${event.title}|${event.source}`));
    return seen.size;
  }

  function updateImportantEventStatus(fetched) {
    const count = importantEventCount();
    const state = showImportantEvents ? "表示ON" : "表示OFF";
    $("importantEventStatus").textContent =
      `${state} / キャッシュ・登録済み ${count}件` +
      (fetched ? " / 取得を実行しました" : "");
  }

  async function fetchImportantEventsForCurrentStock() {
    if (!stockData?.symbol) {
      $("importantEventStatus").textContent = "先に銘柄を検索してください。";
      return;
    }
    $("fetchImportantEvents").disabled = true;
    finishSearchProgress(true);
    setRunStatus(`${stockData.symbol}：重要開示日を取得しています…`);
    setRunStatus(`${stockData.symbol}：重要開示日を取得しています… ${importantEventEstimateText()}`);
    startEventProgress();
    $("importantEventStatus").textContent = `重要開示日を取得しています… ${importantEventEstimateText()}`;
    const displayStart = stockData.points?.[0]?.date || "";
    const displayEnd = stockData.points?.[stockData.points.length - 1]?.date || "";
    try {
      const response = await fetch("/api/important-events/fetch", {
        method:"POST",
        headers:{"Content-Type":"application/json"},
        body:JSON.stringify({symbol:stockData.symbol, displayStart, displayEnd})
      });
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "重要開示日を取得できませんでした。");
      stockData.importantEvents = body.importantEvents || [];
      if (stockData.stability) {
        stockData.stability.importantEvents = body.allImportantEvents || [];
      }
      updateImportantEventStatus(true);
      drawPriceChart();
      drawStabilityChart();
      setRunStatus(`${stockData.symbol}：重要開示日取得完了・${importantEventCount()}件を表示対象にしました`);
      finishEventProgress(true);
    } catch (error) {
      $("importantEventStatus").textContent = error.message;
      setRunStatus(error.message);
      finishEventProgress(false);
    } finally {
      $("fetchImportantEvents").disabled = false;
    }
  }

  async function searchStock() {
    const symbol = $("symbol").value.trim();
    if (!symbol) {
      showError("銘柄コードを入力してください。");
      $("symbol").focus();
      return;
    }
    setLoading(true, "通常チャートと日足を取得し、底練り状態を分析しています…");
    setRunStatus(`検索・分析中です… ${searchEstimateText()}`);
    startSearchProgress();
    const query = new URLSearchParams({
      symbol,
      market:$("market").value,
      period:$("period").value,
      securityType:$("securityType").value,
      algorithmMode:$("algorithmMode").value,
      analysisStart:$("analysisStart").value,
      analysisEnd:$("analysisEnd").value,
      delayedBuyDays:$("delayedBuyDays").value,
      enableDelayedBuy:$("enableDelayedBuy").checked,
      drawdownBuyPercent:$("drawdownBuyPercent").value,
      enableDrawdownBuy:$("enableDrawdownBuy").checked,
      drawdownMissZero:$("drawdownMissZero").checked
    });
    try {
      const response = await fetch("/api/stock?" + query.toString());
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "データを取得できませんでした。");
      stockData = body;
      $("fetchImportantEvents").disabled = false;
      updateImportantEventStatus(false);
      updateMetrics(body);
      updateStability(body.stability);
      drawPriceChart();
      drawStabilityChart();
      $("statusText").textContent =
        `${body.symbol}：底練り分析完了・日足${body.cache.savedPriceCount.toLocaleString()}件を保存`;
      setRunStatus($("statusText").textContent);
      $("status").classList.remove("loading", "error");
      finishSearchProgress(true);
      refreshCacheStatus();
    } catch (error) {
      showError(error.message);
      finishSearchProgress(false);
    } finally {
      $("search").disabled = false;
    }
  }

  function updateMetrics(data) {
    $("company").textContent =
      `${data.name} (${data.symbol})${data.exchange ? " / " + data.exchange : ""}`;
    $("latest").textContent = money(data.latest.price, data.currency);
    $("latestDate").textContent = data.latest.date;
    $("highest").textContent = money(data.highest.price, data.currency);
    $("highestDate").textContent = data.highest.date;
    $("lowest").textContent = money(data.lowest.price, data.currency);
    $("lowestDate").textContent = data.lowest.date;
    const sign = data.changePercent >= 0 ? "+" : "";
    $("change").textContent = `${sign}${data.changePercent.toFixed(2)}%`;
    $("change").style.color = data.changePercent >= 0 ? "#059669" : "#dc2626";
  }

  function updateStability(data) {
    $("stabilityPanel").classList.remove("hidden");
    const backtest = data.backtest || {};
    const formatBacktest = (windowDays) => {
      const item = (backtest.windows || {})[String(windowDays)];
      if (!item || !item.count) return "—";
      return `${item.averagePercent.toFixed(1)}% / ${(item.winRate * 100).toFixed(0)}%`;
    };
    $("backtestSignals").textContent = `${backtest.signalCount || 0}回`;
    $("backtest5").textContent = formatBacktest(5);
    $("backtest20").textContent = formatBacktest(20);
    $("backtest60").textContent = formatBacktest(60);
    updateBottomCandidates(data);
    const scope = data.analysisScope || {};
    const scopeLabel = scope.custom
      ? `手動範囲 ${scope.effectiveStart || "—"}〜${scope.effectiveEnd || "—"}（${scope.tradingDays || 0}営業日）`
      : `通常範囲 ${scope.effectiveStart || data.listingDate || "—"}〜${scope.effectiveEnd || data.dataEndDate || "—"}`;
    const modeLabel = data.algorithmMode === "ipo"
      ? "上場後特化モード"
      : "汎用モード";
    const badge = $("stabilityBadge");
    if (!data.detected) {
      badge.className = "badge waiting";
      badge.textContent = "底打ち候補未検出";
      $("stableDate").textContent = "未検出";
      $("stableTiming").textContent = `${modeLabel} / ${scopeLabel} / ${data.reason || ""}`;
      ["priceLocationScore","volatilityScore","sidewaysScore","trendScore"].forEach(id => $(id).textContent = "—");
      ["priceLocationBar","volatilityBar","sidewaysBar","trendBar"].forEach(id => $(id).style.width = "0");
      $("priceLocationDetail").textContent =
        `大調整条件：株式${data.config.drawdownPercent}%以上 / ETFは商品区分で緩和`;
      $("volatilityDetail").textContent =
        `20日平均絶対騰落率 ${data.config.maxAbsReturnPercent}%以下`;
      $("sidewaysDetail").textContent = "";
      $("trendDetail").textContent =
        `底打ちトリガー ${data.priceTriggerCount ?? 0}回 / ピーク過熱 ${data.peakOverheatCount ?? 0}日 / 強警戒 ${data.peakWarningCount ?? 0}日`;
      return;
    }

    badge.className = "badge detected";
    badge.textContent = `底打ち候補検出・総合${data.scoreAtStable}点`;
    $("stableDate").textContent = data.stableDate;
    $("stableTiming").textContent =
      `${modeLabel} / ${scopeLabel} / 分析開始日から${data.calendarDaysToStable.toLocaleString()}日（約${data.monthsToStable}か月）`;

    const components = data.componentsAtStable;
    const metrics = data.metricsAtStable;
    $("priceLocationScore").textContent = `${components.priceLocation} / 30点`;
    $("volatilityScore").textContent = `${components.volatility} / 20点`;
    $("sidewaysScore").textContent = `${components.sideways} / 25点`;
    $("trendScore").textContent = `${components.trend} / 25点`;
    $("priceLocationBar").style.width = `${components.priceLocation / 30 * 100}%`;
    $("volatilityBar").style.width = `${components.volatility / 20 * 100}%`;
    $("sidewaysBar").style.width = `${components.sideways / 25 * 100}%`;
    $("trendBar").style.width = `${components.trend / 25 * 100}%`;
    $("priceLocationDetail").textContent =
      data.algorithmMode === "ipo"
        ? `上場後高値から最大 ${metrics.recentLowDrawdownPercent.toFixed(1)}%下落後に反発 / 現在は高値から${metrics.drawdownPercent.toFixed(1)}%下落`
        : `過去500日高値から ${metrics.drawdownPercent.toFixed(1)}%下落 / 高値から${metrics.peakAgeTradingDays}営業日`;
    $("volatilityDetail").textContent =
      `20日平均絶対騰落率 ${metrics.volatility20}%`;
    $("sidewaysDetail").textContent =
      `60日終値レンジ ${metrics.range60}%`;
    const triggerNames = {
      volume_breakout_confirmed:"60日レンジ突破＋出来高・2日確認",
      volume_expansion_confirmed:"+5%以上＋出来高急増・2日確認",
      ipo_breakout_confirmed:"上場後特化：60日レンジ突破・2日確認",
      ipo_expansion_confirmed:"上場後特化：+5%以上上昇・2日確認"
    };
    $("trendDetail").textContent =
      `${triggerNames[metrics.triggerType] || "価格上放れ確認"} / 起点 ${metrics.triggerEventDate || data.stableDate} / ピーク過熱 ${data.peakOverheatCount ?? 0}日 / 強警戒 ${data.peakWarningCount ?? 0}日`;
  }

  function fitCanvas(canvas) {
    const rect = canvas.getBoundingClientRect();
    const ratio = window.devicePixelRatio || 1;
    canvas.width = Math.round(rect.width * ratio);
    canvas.height = Math.round(rect.height * ratio);
    const context = canvas.getContext("2d");
    context.setTransform(ratio,0,0,ratio,0,0);
    return {ctx:context, width:rect.width, height:rect.height};
  }

  function drawEmpty(ctx, width, height, message) {
    ctx.fillStyle = "#64748b";
    ctx.textAlign = "center";
    ctx.font = '14px "Yu Gothic UI",sans-serif';
    ctx.fillText(message, width / 2, height / 2);
  }

  function drawAxes(ctx, data, bounds, min, max, currency, valueFormatter) {
    const {left,top,right,bottom} = bounds;
    const height = bottom - top;
    ctx.font = '11px "Yu Gothic UI",sans-serif';
    ctx.textBaseline = "middle";
    for (let i = 0; i <= 5; i++) {
      const py = top + i * height / 5;
      const value = max - i * (max - min) / 5;
      ctx.strokeStyle = "#dce3ec";
      ctx.setLineDash([2,4]);
      ctx.beginPath(); ctx.moveTo(left,py); ctx.lineTo(right,py); ctx.stroke();
      ctx.fillStyle = "#64748b";
      ctx.textAlign = "right";
      ctx.fillText(valueFormatter ? valueFormatter(value) : money(value,currency), left - 9, py);
    }
    const count = Math.min(6,data.length);
    ctx.setLineDash([]);
    ctx.textBaseline = "top";
    for (let i = 0; i < count; i++) {
      const index = count === 1 ? 0 : Math.round(i * (data.length - 1) / (count - 1));
      const px = data.length === 1 ? left : left + index * (right - left) / (data.length - 1);
      ctx.strokeStyle = "#edf1f6";
      ctx.beginPath(); ctx.moveTo(px,top); ctx.lineTo(px,bottom); ctx.stroke();
      ctx.fillStyle = "#64748b";
      ctx.textAlign = i === 0 ? "left" : (i === count - 1 ? "right" : "center");
      ctx.fillText(data[index].date,px,bottom + 13);
    }
  }

  function chartEvents(data, events) {
    if (!data?.length || !events?.length) return [];
    const indexByDate = new Map(data.map((item,index) => [item.date,index]));
    return events
      .map(event => ({...event, index:indexByDate.get(event.chartDate || event.eventDate)}))
      .filter(event => event.index != null);
  }

  function drawImportantEventLines(ctx, data, bounds, events, fullHeightBottom) {
    if (!showImportantEvents) return;
    const matched = chartEvents(data, events);
    if (!matched.length) return;
    const x = index => data.length === 1 ? bounds.left :
      bounds.left + index * (bounds.right - bounds.left) / (data.length - 1);
    matched.forEach(event => {
      const eventX = x(event.index);
      if (event.material) {
        ctx.fillStyle = "rgba(168,85,247,.12)";
        ctx.fillRect(eventX - 3,bounds.top,6,(fullHeightBottom || bounds.bottom) - bounds.top);
      }
      ctx.strokeStyle = event.material ? "#7c3aed" : "#eab308";
      ctx.lineWidth = event.material ? 1.7 : 1.1;
      ctx.setLineDash(event.material ? [6,3] : [2,4]);
      ctx.beginPath();
      ctx.moveTo(eventX,bounds.top);
      ctx.lineTo(eventX,fullHeightBottom || bounds.bottom);
      ctx.stroke();
    });
    ctx.setLineDash([]);
  }

  function eventTooltipHtml(dateText) {
    if (!showImportantEvents) return "";
    const events = [
      ...(stockData?.importantEvents || []),
      ...(stockData?.stability?.importantEvents || [])
    ].filter(event => (event.chartDate || event.eventDate) === dateText);
    if (!events.length) return "";
    const unique = [];
    const seen = new Set();
    events.forEach(event => {
      const key = `${event.eventDate}|${event.title}|${event.source}`;
      if (!seen.has(key)) { seen.add(key); unique.push(event); }
    });
    return "<hr>" + unique.map(event => {
      const impact = event.impactPercent == null ? "" : ` / 前後変動 ${event.impactPercent}%`;
      const volume = event.volumeRatio == null ? "" : ` / 出来高 ${event.volumeRatio}倍`;
      const flag = event.material ? "材料確認ゾーン" : "重要日";
      return `<strong>${flag}</strong>：${escapeHtml(event.category || "")} ` +
        `${escapeHtml(event.eventDate || "")}<br>` +
        `${escapeHtml(event.title || "")}<br>` +
        `<span style="color:#64748b">${escapeHtml(event.source || "")}${impact}${volume}</span>`;
    }).join("<br>");
  }

  function drawPriceChart() {
    const canvas = $("priceChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    if (!stockData?.points?.length) {
      drawEmpty(ctx,width,height,"銘柄コードを入力して「検索・分析」を押してください");
      return;
    }
    const data = stockData.points;
    const values = data.map(item => item.close);
    let min = Math.min(...values), max = Math.max(...values);
    let spread = max - min || Math.max(Math.abs(max) * .02,1);
    min -= spread * .08; max += spread * .08;
    const bounds = {left:82,top:22,right:width-20,bottom:height-44};
    drawAxes(ctx,data,bounds,min,max,stockData.currency);
    const x = index => data.length === 1 ? bounds.left :
      bounds.left + index * (bounds.right - bounds.left) / (data.length - 1);
    const y = value => bounds.top + (max - value) * (bounds.bottom - bounds.top) / (max - min);
    drawImportantEventLines(ctx,data,bounds,stockData.importantEvents || []);

    ctx.beginPath();
    data.forEach((item,index) => index ? ctx.lineTo(x(index),y(item.close)) : ctx.moveTo(x(index),y(item.close)));
    ctx.lineTo(x(data.length-1),bounds.bottom); ctx.lineTo(x(0),bounds.bottom); ctx.closePath();
    const gradient = ctx.createLinearGradient(0,bounds.top,0,bounds.bottom);
    gradient.addColorStop(0,"rgba(37,99,235,.25)");
    gradient.addColorStop(1,"rgba(37,99,235,.02)");
    ctx.fillStyle = gradient; ctx.fill();
    ctx.beginPath();
    data.forEach((item,index) => index ? ctx.lineTo(x(index),y(item.close)) : ctx.moveTo(x(index),y(item.close)));
    ctx.strokeStyle = "#2563eb"; ctx.lineWidth = 2.4; ctx.lineJoin = "round"; ctx.stroke();
    chartViews.price = {canvas,data,bounds,min,max,currency:stockData.currency,events:stockData.importantEvents || []};
  }

  function drawStabilityChart() {
    const canvas = $("stabilityChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    const analysis = stockData?.stability;
    const data = analysis?.series || [];
    if (!data.length) {
      drawEmpty(ctx,width,height,analysis?.reason || "底練り分析データがありません");
      return;
    }
    const priceValues = [];
    data.forEach(item => {
      priceValues.push(item.close);
      if (item.ma25 != null) priceValues.push(item.ma25);
      if (item.ma75 != null) priceValues.push(item.ma75);
    });
    let min = Math.min(...priceValues), max = Math.max(...priceValues);
    let spread = max - min || Math.max(Math.abs(max) * .02,1);
    min -= spread * .06; max += spread * .06;
    const priceBounds = {left:82,top:38,right:width-20,bottom:height-155};
    const scoreBounds = {left:82,top:height-116,right:width-20,bottom:height-38};
    const x = index => data.length === 1 ? priceBounds.left :
      priceBounds.left + index * (priceBounds.right - priceBounds.left) / (data.length - 1);
    const priceY = value => priceBounds.top + (max-value) *
      (priceBounds.bottom-priceBounds.top)/(max-min);
    const scoreY = value => scoreBounds.bottom - value *
      (scoreBounds.bottom-scoreBounds.top)/100;

    data.forEach((item,index) => {
      if (!item.peakOverheat) return;
      const nextX = index === data.length-1 ? priceBounds.right : x(index+1);
      ctx.fillStyle = "rgba(245,158,11,.08)";
      ctx.fillRect(x(index),priceBounds.top,Math.max(1,nextX-x(index)),priceBounds.bottom-priceBounds.top);
      ctx.fillRect(x(index),scoreBounds.top,Math.max(1,nextX-x(index)),scoreBounds.bottom-scoreBounds.top);
    });
    data.forEach((item,index) => {
      if (!item.peakCandidate) return;
      const nextX = index === data.length-1 ? priceBounds.right : x(index+1);
      ctx.fillStyle = "rgba(245,158,11,.24)";
      ctx.fillRect(x(index),priceBounds.top,Math.max(1,nextX-x(index)),priceBounds.bottom-priceBounds.top);
      ctx.fillRect(x(index),scoreBounds.top,Math.max(1,nextX-x(index)),scoreBounds.bottom-scoreBounds.top);
    });
    data.forEach((item,index) => {
      if (!item.eligible) return;
      const nextX = index === data.length-1 ? priceBounds.right : x(index+1);
      ctx.fillStyle = "rgba(16,185,129,.10)";
      ctx.fillRect(x(index),priceBounds.top,Math.max(1,nextX-x(index)),priceBounds.bottom-priceBounds.top);
      ctx.fillRect(x(index),scoreBounds.top,Math.max(1,nextX-x(index)),scoreBounds.bottom-scoreBounds.top);
    });
    drawAxes(ctx,data,priceBounds,min,max,stockData.currency);
    drawImportantEventLines(ctx,data,priceBounds,analysis.importantEvents || [],scoreBounds.bottom);

    function drawSeries(key,color,widthValue) {
      ctx.beginPath(); let started = false;
      data.forEach((item,index) => {
        if (item[key] == null) { started = false; return; }
        if (!started) { ctx.moveTo(x(index),priceY(item[key])); started = true; }
        else ctx.lineTo(x(index),priceY(item[key]));
      });
      ctx.strokeStyle = color; ctx.lineWidth = widthValue; ctx.setLineDash([]); ctx.stroke();
    }
    drawSeries("close","#2563eb",2);
    drawSeries("ma25","#d97706",1.6);
    drawSeries("ma75","#7c3aed",1.8);

    ctx.font = 'bold 11px "Yu Gothic UI",sans-serif';
    [["終値","#2563eb"],["25日線","#d97706"],["75日線","#7c3aed"]].forEach((item,index) => {
      const lx = priceBounds.left + index * 78;
      ctx.strokeStyle = item[1]; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(lx,18); ctx.lineTo(lx+18,18); ctx.stroke();
      ctx.fillStyle = item[1]; ctx.textAlign = "left"; ctx.textBaseline = "middle";
      ctx.fillText(item[0],lx+23,18);
    });

    ctx.strokeStyle = "#dce3ec"; ctx.lineWidth = 1; ctx.setLineDash([]);
    ctx.strokeRect(scoreBounds.left,scoreBounds.top,scoreBounds.right-scoreBounds.left,scoreBounds.bottom-scoreBounds.top);
    const thresholdY = scoreY(analysis.config.scoreThreshold);
    ctx.strokeStyle = "#dc2626"; ctx.setLineDash([5,4]);
    ctx.beginPath(); ctx.moveTo(scoreBounds.left,thresholdY); ctx.lineTo(scoreBounds.right,thresholdY); ctx.stroke();
    ctx.fillStyle = "#dc2626"; ctx.textAlign = "right"; ctx.textBaseline = "bottom";
    ctx.fillText(`${analysis.config.scoreThreshold}点`,scoreBounds.left-8,thresholdY);
    ctx.fillStyle = "#64748b"; ctx.textAlign = "right"; ctx.textBaseline = "middle";
    ctx.fillText("100",scoreBounds.left-8,scoreBounds.top);
    ctx.fillText("0",scoreBounds.left-8,scoreBounds.bottom);
    ctx.fillStyle = "#475569"; ctx.textAlign = "left"; ctx.textBaseline = "bottom";
    ctx.fillText("緑＝底練り候補 / 薄黄＝過熱 / 濃黄・赤線＝ピーク強警戒",scoreBounds.left,scoreBounds.top-7);

    ctx.beginPath(); let scoreStarted = false;
    data.forEach((item,index) => {
      if (item.score == null) { scoreStarted = false; return; }
      if (!scoreStarted) { ctx.moveTo(x(index),scoreY(item.score)); scoreStarted = true; }
      else ctx.lineTo(x(index),scoreY(item.score));
    });
    ctx.strokeStyle = "#059669"; ctx.lineWidth = 2; ctx.setLineDash([]); ctx.stroke();

    ctx.beginPath(); let peakScoreStarted = false;
    data.forEach((item,index) => {
      if (item.peakScore == null) { peakScoreStarted = false; return; }
      if (!peakScoreStarted) { ctx.moveTo(x(index),scoreY(item.peakScore)); peakScoreStarted = true; }
      else ctx.lineTo(x(index),scoreY(item.peakScore));
    });
    ctx.strokeStyle = "#f59e0b"; ctx.lineWidth = 1.7; ctx.setLineDash([]); ctx.stroke();

    data.forEach((item,index) => {
      if (!item.peakCandidate) return;
      const peakX = x(index);
      ctx.strokeStyle = "#ef4444";
      ctx.lineWidth = 1.5;
      ctx.setLineDash([3,3]);
      ctx.beginPath();
      ctx.moveTo(peakX,priceBounds.top);
      ctx.lineTo(peakX,scoreBounds.bottom);
      ctx.stroke();
    });
    ctx.setLineDash([]);

    data.forEach((item,index) => {
      if (!item.priceTrigger) return;
      const crossX = x(index);
      const selectedCross = analysis.detected && item.date === analysis.stableDate;
      ctx.strokeStyle = selectedCross ? "#059669" : "#d97706";
      ctx.lineWidth = selectedCross ? 2 : 1;
      ctx.setLineDash(selectedCross ? [] : [3,4]);
      ctx.beginPath();
      ctx.moveTo(crossX,priceBounds.top);
      ctx.lineTo(crossX,priceBounds.bottom);
      ctx.stroke();
    });

    if (analysis.detected) {
      const stableIndex = data.findIndex(item => item.date === analysis.stableDate);
      if (stableIndex >= 0) {
        const stableItem = data[stableIndex];
        const stableX = x(stableIndex);
        ctx.strokeStyle = "#059669"; ctx.lineWidth = 2; ctx.setLineDash([6,4]);
        ctx.beginPath(); ctx.moveTo(stableX,priceBounds.top); ctx.lineTo(stableX,scoreBounds.bottom); ctx.stroke();
        ctx.fillStyle = "#047857";
        ctx.textAlign = stableX > width * .72 ? "right" : "left";
        ctx.textBaseline = "top";
        ctx.fillText(`底打ち候補 ${analysis.stableDate} / ${money(stableItem.close, stockData.currency)}`,stableX + (stableX > width*.72 ? -6 : 6),priceBounds.top+5);
      }
    }
    chartViews.stability = {canvas,data,bounds:priceBounds,scoreBounds,min,max,currency:stockData.currency,events:analysis.importantEvents || []};
  }

  function setCacheButtonsDisabled(disabled) {
    ["cacheUpdate","cacheAnalyzeMissing","cacheReanalyze","cacheShow","marketCapCsvImport"].forEach(
      id => $(id).disabled = disabled
    );
  }

  async function refreshCacheStatus(updateMessage = true) {
    try {
      const response = await fetch("/api/cache/status");
      const data = await response.json();
      if (!response.ok) throw new Error(data.error || "保存状況を取得できませんでした。");
      $("cacheStockCount").textContent = `${data.stockCount.toLocaleString()}社`;
      $("cachePriceCount").textContent = `${data.priceCount.toLocaleString()}件`;
      $("cacheAnalysisCount").textContent = `${data.analysisCount.toLocaleString()}社`;
      $("cacheDetectedCount").textContent = `${data.detectedCount.toLocaleString()}社`;
      $("cacheVersion").className = "badge detected";
      $("cacheVersion").textContent = `判定版 ${data.algorithmVersion}`;
      if (updateMessage && data.lastUpdated) {
        $("cacheMessage").textContent =
          `最終保存: ${data.lastUpdated} / 保存先: ${data.databasePath}`;
      }
    } catch (error) {
      $("cacheVersion").className = "badge waiting";
      $("cacheVersion").textContent = "保存状態エラー";
      $("cacheMessage").textContent = error.message;
    }
  }

  async function runCacheAction(path, workingMessage) {
    setCacheButtonsDisabled(true);
    $("cacheMessage").textContent = workingMessage;
    try {
      const response = await fetch(path, {method:"POST"});
      const data = await response.json();
      if (!response.ok) throw new Error(data.error || "処理に失敗しました。");
      const errorCount = (data.errors || []).length;
      if ("updatedCount" in data) {
        $("cacheMessage").textContent =
          `${data.targetCount}社を確認し、${data.updatedCount}社を追加更新、${data.skippedCount}社を省略しました。エラー${errorCount}件。`;
      } else {
        $("cacheMessage").textContent =
          `${data.targetCount}社中${data.completedCount}社を再計算しました。エラー${errorCount}件。`;
      }
      await refreshCacheStatus(false);
    } catch (error) {
      $("cacheMessage").textContent = error.message;
    } finally {
      setCacheButtonsDisabled(false);
    }
  }

  async function importMarketCapCsvFile(file) {
    if (!file) return;
    $("cacheMessage").textContent = `${file.name} を読み込んでいます…`;
    try {
      const csvText = await file.text();
      const response = await fetch("/api/market-cap/import", {
        method:"POST",
        headers:{"Content-Type":"application/json"},
        body:JSON.stringify({csvText, filename:file.name})
      });
      const data = await response.json();
      if (!response.ok) throw new Error(data.error || "時価総額CSVを読み込めませんでした。");
      const sampleErrors = (data.errors || []).slice(0,3)
        .map(item => `行${item.line}: ${item.reason}`)
        .join(" / ");
      $("cacheMessage").textContent =
        `時価総額CSV読込完了：${data.imported.toLocaleString()}件保存、${data.skipped.toLocaleString()}件スキップ` +
        (sampleErrors ? `（例：${sampleErrors}）` : "");
    } catch (error) {
      $("cacheMessage").textContent = error.message;
    } finally {
      $("marketCapCsvFile").value = "";
    }
  }

  async function showCachedResults() {
    setCacheButtonsDisabled(true);
    $("cacheMessage").textContent = "保存済みの分析結果を読み込んでいます…";
    try {
      const response = await fetch("/api/cache/results");
      const data = await response.json();
      if (!response.ok) throw new Error(data.error || "保存結果を取得できませんでした。");
      batchData = data.results;
      updateBatchTable();
      drawHistogram();
      const detected = batchData.filter(item => item.detected).length;
      $("batchStatus").textContent =
        `保存済み${batchData.length}社中${detected}社で底打ち候補を検出しています。`;
      $("cacheMessage").textContent =
        `${batchData.length}社の保存結果を買い方ランキング集計へ表示しました。`;
    } catch (error) {
      $("cacheMessage").textContent = error.message;
    } finally {
      setCacheButtonsDisabled(false);
    }
  }

  const DEFAULT_BATCH_SYMBOLS = "7203\n6758\nAAPL\nVOO|ETF";

  function normalizedBatchSymbols(value) {
    return value.trim().replace(/\r\n/g, "\n").replace(/\r/g, "\n");
  }

  async function analyzeBatch(options = {}) {
    const rawSymbols = $("batchSymbols").value;
    const sortByMarketCap = !!options.sortByMarketCap;
    let universe = $("batchUniverse").value;
    let symbols = rawSymbols.trim();
    if ((sortByMarketCap || universe !== "manual") && normalizedBatchSymbols(rawSymbols) === DEFAULT_BATCH_SYMBOLS) {
      symbols = "";
      if (universe === "manual") universe = "known";
    }
    const mode = $("batchMode").value;
    const runUntilLimit = !!options.runUntilLimit;
    const delayedBuyDays = $("delayedBuyDays").value;
    const enableDelayedBuy = $("enableDelayedBuy").checked;
    const drawdownBuyPercent = $("drawdownBuyPercent").value;
    const enableDrawdownBuy = $("enableDrawdownBuy").checked;
    const drawdownMissZero = $("drawdownMissZero").checked;
    const disableSavedAnalysisReuse = $("disableSavedAnalysisReuse").checked;
    if (!symbols && !sortByMarketCap && universe === "manual") {
      $("batchStatus").textContent = "銘柄コードを入力してください。";
      return;
    }
    $("batchAnalyze").disabled = true;
    $("batchMarketCapAnalyze").disabled = true;
    $("batchCancel").disabled = true;
    $("batchCsv").disabled = true;
    const usingKnownUniverse = sortByMarketCap && !symbols;
    $("batchStatus").textContent = usingKnownUniverse
      ? "保存済み＋候補リストを時価総額順に並べ替えて、連続分析を開始しています…"
      : sortByMarketCap
      ? "時価総額順に並べ替えて、連続分析を開始しています…"
      : "まとめて分析を開始しています…";
    try {
      const response = await fetch("/api/batch", {
        method:"POST",
        headers:{"Content-Type":"application/json"},
        body:JSON.stringify({
          symbols, mode, sortByMarketCap, runUntilLimit, universe,
          delayedBuyDays, enableDelayedBuy, drawdownBuyPercent,
          enableDrawdownBuy, drawdownMissZero, disableSavedAnalysisReuse
        })
      });
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "まとめて分析を開始できませんでした。");
      currentBatchJobId = body.jobId;
      batchData = body.results || [];
      updateBatchProgress(body);
      $("batchCancel").disabled = false;
      if (batchPollTimer) clearInterval(batchPollTimer);
      batchPollTimer = setInterval(pollBatchJob, 900);
      await pollBatchJob();
    } catch (error) {
      $("batchStatus").textContent = error.message;
      $("batchAnalyze").disabled = false;
      $("batchMarketCapAnalyze").disabled = false;
      $("batchCancel").disabled = true;
    }
  }

  async function pollBatchJob() {
    if (!currentBatchJobId) return;
    try {
      const response = await fetch("/api/batch/status?jobId=" + encodeURIComponent(currentBatchJobId));
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "進捗を取得できませんでした。");
      updateBatchProgress(body);
      if (["completed","canceled"].includes(body.status)) {
        clearInterval(batchPollTimer);
        batchPollTimer = null;
        currentBatchJobId = null;
        $("batchAnalyze").disabled = false;
        $("batchMarketCapAnalyze").disabled = false;
        $("batchCancel").disabled = true;
        refreshCacheStatus();
      }
    } catch (error) {
      $("batchStatus").textContent = error.message;
      clearInterval(batchPollTimer);
      batchPollTimer = null;
      currentBatchJobId = null;
      $("batchAnalyze").disabled = false;
      $("batchMarketCapAnalyze").disabled = false;
      $("batchCancel").disabled = true;
    }
  }

  function updateBatchProgress(body) {
    batchData = body.results || [];
    const detected = batchData.filter(item => item.detected).length;
    const errors = (body.errors || []).length;
    const statusLabel = body.status === "completed"
      ? "完了"
      : body.status === "canceled"
        ? (body.stopReason === "rate_limit" ? "取得制限で停止" : "中断済み")
        : body.status === "canceling"
          ? "中断処理中"
          : "分析中";
      const current = body.current ? ` / 処理中：${body.current}` : "";
    const modeLabel = body.mode === "ipo" ? "上場後特化" : body.mode === "both" ? "両方" : "汎用";
    const runLabel = body.runUntilLimit ? " / 連続分析" : "";
    const recalcLabel = body.disableSavedAnalysisReuse ? " / 強制再計算" : "";
    const warning = body.warning ? ` / 注意：${body.warning}` : "";
    $("batchStatus").textContent =
      `${statusLabel}：${body.completed || 0}/${body.total || 0}件完了 / ${modeLabel}${runLabel}${recalcLabel}${current} / 底打ち候補 ${detected}件 / エラー ${errors}件${warning}`;
    renderBatchTimingRanking(body);
    updateBatchTable();
    drawHistogram();
  }

  function secondsText(value) {
    const seconds = Number(value) || 0;
    if (seconds >= 60) return `${(seconds / 60).toFixed(1)}分`;
    return `${seconds.toFixed(seconds >= 10 ? 1 : 2)}秒`;
  }

  function renderBatchTimingRanking(body) {
    const panel = $("batchTimingPanel");
    const timings = (body.timingRanking || []).slice(0, 8);
    const symbols = (body.slowestSymbols || []).slice(0, 8);
    if (!timings.length && !symbols.length) {
      panel.classList.add("hidden");
      panel.innerHTML = "";
      return;
    }
    const timingRows = timings.map((item, index) =>
      `<div class="timing-row">
        <span>${index + 1}. ${escapeHtml(item.name)}</span>
        <span>${secondsText(item.totalSeconds)}</span>
        <span>${item.count || 0}回</span>
        <span>${secondsText(item.averageSeconds)}</span>
      </div>`
    ).join("");
    const symbolRows = symbols.map((item, index) =>
      `<div class="timing-row symbol">
        <span>${index + 1}. ${escapeHtml(item.symbol)}</span>
        <span>${escapeHtml(item.name || item.error || "")}</span>
        <span>${secondsText(item.elapsedSeconds)}</span>
      </div>`
    ).join("");
    panel.innerHTML =
      `<div class="timing-grid">
        <div>
          <div class="timing-title">処理に時間がかかっている工程ランキング</div>
          <div class="timing-row header"><span>工程</span><span>合計</span><span>回数</span><span>平均</span></div>
          ${timingRows || '<div class="note">まだ計測対象がありません。</div>'}
        </div>
        <div>
          <div class="timing-title">時間がかかった銘柄ランキング</div>
          <div class="timing-row symbol header"><span>銘柄</span><span>名称/エラー</span><span>時間</span></div>
          ${symbolRows || '<div class="note">まだ完了銘柄がありません。</div>'}
        </div>
      </div>`;
    panel.classList.remove("hidden");
  }

  async function cancelBatch() {
    if (!currentBatchJobId) return;
    $("batchCancel").disabled = true;
    $("batchStatus").textContent = "中断を要求しました。いま処理中の1銘柄が終わったところで止まります…";
    try {
      const response = await fetch("/api/batch/cancel", {
        method:"POST",
        headers:{"Content-Type":"application/json"},
        body:JSON.stringify({jobId:currentBatchJobId})
      });
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "中断できませんでした。");
      updateBatchProgress(body);
    } catch (error) {
      $("batchStatus").textContent = error.message;
    }
  }

  function updateBatchTable() {
    $("batchTableWrap").classList.remove("hidden");
    $("batchCsv").disabled = !batchData.length;
    const columns = batchColumns.filter(column => visibleBatchColumns.has(column.key));
    $("batchTableHead").innerHTML =
      `<tr>${columns.map(column => `<th>${column.label}</th>`).join("")}</tr>`;
    $("batchTableBody").innerHTML = batchData.map(item => {
      if (item.error) {
        return `<tr><td>${escapeHtml(item.input)}</td><td colspan="${Math.max(columns.length - 2, 1)}">—</td><td style="color:#dc2626">${escapeHtml(item.error)}</td></tr>`;
      }
      return `<tr>${columns.map(column => `<td>${column.render(item)}</td>`).join("")}</tr>`;
    }).join("");
  }

  function renderBatchColumnPicker() {
    const box = $("batchColumnOptions");
    const groupNames = {
      base:"基本情報",
      price:"価格・規模",
      bottom:"底判定",
      return:"リターン",
      simulation:"買い方比較",
      verdict:"判定"
    };
    const groupForColumn = column => {
      if (column.group) return column.group;
      if (["symbol","name","algorithmMode","listingDate","stableDate","calendarDaysToStable"].includes(column.key)) return "基本情報";
      if (["stablePrice","previousPeak","currentPrice","minAfter","maxBeforeActualBottom"].includes(column.key)) return "価格・規模";
      if (["bottomPositionRatio","drawdownFromPreviousPeakPercent","drawdownAfterPercent","daysToMin","bottomVerdict","detected","riseBeforeActualBottomPercent"].includes(column.key)) return "底判定";
      if (["holdingReturnPercent","annualizedReturnPercent","holdingDays"].includes(column.key)) return "リターン";
      if (column.key.includes("delayed") || column.key.includes("drawdown") || column.key.includes("benchmark") || column.key.includes("Rank")) return "買い方比較";
      return "その他";
    };
    const groups = new Map();
    batchColumns.forEach(column => {
      const group = groupForColumn(column);
      if (!groups.has(group)) groups.set(group, []);
      groups.get(group).push(column);
    });
    box.innerHTML = Array.from(groups.entries()).map(([group, columns]) =>
      `<div class="column-group">
        <div class="column-group-title">${escapeHtml(group)}</div>
        <div class="column-group-items">
          ${columns.map(column =>
            `<label><input type="checkbox" value="${column.key}" ${visibleBatchColumns.has(column.key) ? "checked" : ""}>${column.label}</label>`
          ).join("")}
        </div>
      </div>`
    ).join("");
    box.querySelectorAll("input").forEach(input => input.addEventListener("change", () => {
      if (input.checked) visibleBatchColumns.add(input.value);
      else visibleBatchColumns.delete(input.value);
      if (!visibleBatchColumns.size) {
        visibleBatchColumns.add("symbol");
        box.querySelector('input[value="symbol"]').checked = true;
      }
      if (batchData.length) updateBatchTable();
    }));
  }

  function setBatchColumns(mode) {
    visibleBatchColumns = new Set(
      batchColumns
        .filter(column => mode === "all" || column.basic)
        .map(column => column.key)
    );
    renderBatchColumnPicker();
    if (batchData.length) updateBatchTable();
  }

  function csvCell(value) {
    const text = String(value ?? "");
    return `"${text.replace(/"/g,'""')}"`;
  }

  function batchCsvRows() {
    const headers = [
      "入力値",
      "銘柄",
      "名称",
      "採用モード",
      "上場日代理",
      "底打ち候補日",
      "通貨",
      "円換算レート",
      "底打ち候補価格（円）",
      "底検知時の推定時価総額（円）",
      "現在の時価総額（円）",
      "経過日数",
      "判定前最高値日",
      "判定前最高値（円）",
      "高値からの下落率",
      "底位置指数",
      "実底前最高値日",
      "実底前最高値（円）",
      "実底前上昇率",
      "現在日",
      "現在価格（円）",
      "現在まで保有リターン",
      "年利換算",
      "保有営業日",
      "保有暦日",
      "遅延買付営業日",
      "遅延買付日",
      "遅延買付価格（円）",
      "遅延買付リターン",
      "遅延買付年利換算",
      "遅延後保有営業日",
      "遅延後保有暦日",
      "下落待ち買付率",
      "下落待ち目標価格（円）",
      "下落待ち買付日",
      "下落待ち買付価格（円）",
      "下落待ちリターン",
      "下落待ち年利換算",
      "下落待ち保有営業日",
      "下落待ち保有暦日",
      "候補後最安値日",
      "候補後最安値（円）",
      "候補後下落率",
      "実底まで営業日",
      "実底まで暦日",
      "成否",
      "判定",
      "エラー",
      "エラー分類"
    ];
    const rows = batchData.map(item => [
      item.input || "",
      item.symbol || "",
      item.name || "",
      item.algorithmMode === "ipo" ? "上場後特化" : item.algorithmMode === "general" ? "汎用" : (item.algorithmMode || ""),
      item.listingDate || "",
      item.stableDate || "",
      item.currency || "",
      item.jpyRate ?? "",
      item.stablePriceJpy ?? "",
      item.estimatedMarketCapAtBottomJpy ?? "",
      item.currentMarketCapJpy ?? "",
      item.calendarDaysToStable ?? "",
      item.previousPeakDate || "",
      item.previousPeakPriceJpy ?? "",
      item.drawdownFromPreviousPeakPercent ?? "",
      item.bottomPositionRatio ?? "",
      item.maxBeforeActualBottomDate || "",
      item.maxBeforeActualBottomPriceJpy ?? "",
      item.riseBeforeActualBottomPercent ?? "",
      item.currentDate || "",
      item.currentPriceJpy ?? "",
      item.holdingReturnPercent ?? "",
      item.annualizedReturnPercent ?? "",
      item.tradingDaysHeld ?? "",
      item.calendarDaysHeld ?? "",
      item.delayedBuyDays ?? "",
      item.delayedBuyDate || "",
      item.delayedBuyPriceJpy ?? "",
      item.delayedHoldingReturnPercent ?? "",
      item.delayedAnnualizedReturnPercent ?? "",
      item.delayedTradingDaysHeld ?? "",
      item.delayedCalendarDaysHeld ?? "",
      item.drawdownBuyPercent ?? "",
      item.drawdownBuyTargetPriceJpy ?? "",
      item.drawdownBuyDate || "",
      item.drawdownBuyPriceJpy ?? "",
      item.drawdownHoldingReturnPercent ?? "",
      item.drawdownAnnualizedReturnPercent ?? "",
      item.drawdownTradingDaysHeld ?? "",
      item.drawdownCalendarDaysHeld ?? "",
      item.minAfterDate || "",
      item.minAfterPriceJpy ?? "",
      item.drawdownAfterPercent ?? "",
      item.tradingDaysToMinAfter ?? "",
      item.calendarDaysToMinAfter ?? "",
      item.bottomVerdict || "",
      item.detected ? "検出" : "未検出",
      item.error || "",
      item.errorCategory || ""
    ]);
    const rankHeaders = [
      "底検知買い順位",
      "遅延買い順位",
      "下落待ち順位",
      "オルカン相当購入日",
      "オルカン相当リターン",
      "オルカン相当順位"
    ];
    headers.splice(headers.length - 2, 0, ...rankHeaders);
    rows.forEach((row, index) => {
      const item = batchData[index] || {};
      row.splice(
        row.length - 2,
        0,
        item.immediateBuyRank ?? "",
        item.delayedBuyRank ?? "",
        item.drawdownBuyRank ?? "",
        item.benchmarkBuyDate || "",
        item.benchmarkHoldingReturnPercent ?? "",
        item.benchmarkBuyRank ?? ""
      );
    });
    return [headers, ...rows];
  }

  function exportBatchCsv() {
    if (!batchData.length) {
      $("batchStatus").textContent = "CSVに出力できる分析結果がありません。";
      return;
    }
    const csv = "\ufeff" + batchCsvRows()
      .map(row => row.map(csvCell).join(","))
      .join("\r\n");
    const blob = new Blob([csv], {type:"text/csv;charset=utf-8"});
    const url = URL.createObjectURL(blob);
    const timestamp = new Date().toISOString().slice(0,19).replace(/[-:T]/g,"");
    const link = document.createElement("a");
    link.href = url;
    link.download = `stock_analysis_${timestamp}.csv`;
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
    $("batchStatus").textContent = `${batchData.length}件の分析結果をCSVに出力しました。`;
  }

  function escapeHtml(value) {
    return String(value ?? "").replace(/[&<>"']/g, character => ({
      "&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#039;"
    })[character]);
  }

  function syncSimulationControls() {
    $("delayedBuyDays").disabled = !$("enableDelayedBuy").checked;
    $("drawdownBuyPercent").disabled = !$("enableDrawdownBuy").checked;
    $("drawdownMissZero").disabled = !$("enableDrawdownBuy").checked;
  }

  function normalizedChartSymbol(item) {
    let raw = String(item?.symbol || item?.input || "").trim().toUpperCase();
    raw = raw.split("|")[0].trim();
    if (/^\d{4}$/.test(raw)) return `${raw}.T`;
    return raw;
  }

  function chartItemPriority(item) {
    const detectedScore = item?.detected ? 1 : 0;
    const returnValue = Number(item?.holdingReturnPercent);
    const returnScore = Number.isFinite(returnValue) ? returnValue : -Infinity;
    const dateScore = String(item?.stableDate || "");
    return {detectedScore, returnScore, dateScore};
  }

  function pickBetterChartItem(current, candidate) {
    if (!current) return candidate;
    const a = chartItemPriority(current);
    const b = chartItemPriority(candidate);
    if (a.detectedScore !== b.detectedScore) {
      return b.detectedScore > a.detectedScore ? candidate : current;
    }
    if (a.returnScore !== b.returnScore) {
      return b.returnScore > a.returnScore ? candidate : current;
    }
    return b.dateScore > a.dateScore ? candidate : current;
  }

  function dedupeChartItems(items) {
    const bySymbol = new Map();
    items.forEach(item => {
      const key = normalizedChartSymbol(item);
      if (!key) return;
      bySymbol.set(key, pickBetterChartItem(bySymbol.get(key), item));
    });
    return Array.from(bySymbol.values());
  }

  function chartFilterSettings() {
    const yearsText = ($("chartRecentYears")?.value || "").trim();
    if (!yearsText) return {enabled:false, years:null, cutoff:null};
    const years = Number(yearsText);
    if (!Number.isFinite(years) || years <= 0) return {enabled:false, years:null, cutoff:null};
    const cutoff = new Date();
    cutoff.setHours(0,0,0,0);
    cutoff.setFullYear(cutoff.getFullYear() - years);
    return {enabled:true, years, cutoff};
  }

  function passesChartDateFilter(item, settings) {
    if (!item.detected) return !settings.enabled;
    if (!settings.enabled) return true;
    if (!item.stableDate) return false;
    const date = new Date(`${item.stableDate}T00:00:00`);
    if (Number.isNaN(date.getTime())) return false;
    return date >= settings.cutoff;
  }

  function chartBatchFilterInfo() {
    const settings = chartFilterSettings();
    const detectedRows = batchData.filter(item => item.detected);
    const dateFilteredRows = batchData.filter(item => passesChartDateFilter(item, settings));
    const dedupedRows = dedupeChartItems(dateFilteredRows);
    const detectedAfterDate = detectedRows.filter(item => {
      if (!settings.enabled) return true;
      if (!item.stableDate) return false;
      const date = new Date(`${item.stableDate}T00:00:00`);
      if (Number.isNaN(date.getTime())) return false;
      return date >= settings.cutoff;
    });
    const dedupedDetected = dedupedRows.filter(item => item.detected);
    return {
      items: dedupedRows,
      settings,
      rawDetected: detectedRows.length,
      dateFilteredDetected: detectedAfterDate.length,
      uniqueDetected: dedupedDetected.length,
      duplicatesRemoved: Math.max(0, detectedAfterDate.length - dedupedDetected.length),
      excludedByDate: Math.max(0, detectedRows.length - detectedAfterDate.length),
    };
  }

  function chartFilteredBatchData() {
    return chartBatchFilterInfo().items;
  }

  function immediateInvestmentValue(item) {
    const value = Number(item.holdingReturnPercent);
    if (!Number.isFinite(value)) return null;
    return 100 * (1 + value / 100);
  }

  function contributionItems() {
    return chartFilteredBatchData()
      .filter(item => item.detected && item.holdingReturnPercent != null)
      .map(item => {
        const finalValue = immediateInvestmentValue(item);
        if (finalValue == null) return null;
        return {
          symbol:item.symbol || item.input || "",
          name:item.name || "",
          stableDate:item.stableDate || "",
          finalValue,
          contribution:finalValue - 100,
        };
      })
      .filter(Boolean)
      .sort((a,b) => b.contribution - a.contribution);
  }

  function drawContributionBreakdown() {
    const panel = $("contributionPanel");
    if (!$("showContributionBreakdown").checked) {
      panel.classList.add("hidden");
      return;
    }
    panel.classList.remove("hidden");
    const items = contributionItems();
    const topN = Math.max(1, Math.min(50, Number($("contributionTopN").value) || 10));
    const positiveItems = items.filter(item => item.contribution > 0);
    const top = positiveItems.slice(0, topN);
    const otherContribution = positiveItems.slice(topN)
      .reduce((sum,item) => sum + item.contribution, 0);
    const slices = [
      ...top.map((item,index) => ({
        label:item.symbol || `#${index+1}`,
        value:item.contribution,
        color:["#2563eb","#059669","#d97706","#7c3aed","#dc2626","#0891b2","#65a30d","#c026d3","#ea580c","#475569"][index % 10],
      })),
      ...(otherContribution > 0 ? [{label:"その他", value:otherContribution, color:"#cbd5e1"}] : []),
    ];
    const canvas = $("contributionChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    if (!slices.length) {
      drawEmpty(ctx,width,height,"正の寄与額がありません");
    } else {
      const total = slices.reduce((sum,item) => sum + item.value, 0);
      const cx = width/2, cy = height/2+8, radius = Math.min(width,height)*0.34;
      let angle = -Math.PI/2;
      slices.forEach(slice => {
        const next = angle + (slice.value / total) * Math.PI * 2;
        ctx.beginPath();
        ctx.moveTo(cx,cy);
        ctx.arc(cx,cy,radius,angle,next);
        ctx.closePath();
        ctx.fillStyle = slice.color;
        ctx.fill();
        angle = next;
      });
      ctx.fillStyle="#475569"; ctx.font='bold 13px "Yu Gothic UI",sans-serif';
      ctx.textAlign="center"; ctx.textBaseline="top";
      ctx.fillText(`正の寄与 上位${topN}件＋その他`,cx,4);
      ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.fillText(`合計 ${Math.round(total).toLocaleString()}円`,cx,22);
    }
    const allPositive = positiveItems.reduce((sum,item) => sum + item.contribution, 0);
    const totalProfit = items.reduce((sum,item) => sum + item.contribution, 0);
    const rows = items.slice(0, topN).map((item,index) => {
      const share = allPositive > 0 && item.contribution > 0
        ? item.contribution / allPositive * 100
        : 0;
      return `<div class="contribution-row">
        <span>${index+1}</span>
        <span>${escapeHtml(item.symbol)}</span>
        <span>${escapeHtml(item.name || item.stableDate || "")}</span>
        <span>${Math.round(item.finalValue).toLocaleString()}円</span>
        <span>${share.toFixed(1)}%</span>
      </div>`;
    }).join("");
    $("contributionList").innerHTML =
      `<div class="contribution-row header">
        <span>順位</span><span>銘柄</span><span>名称/日付</span><span>評価額</span><span>比率</span>
      </div>` +
      rows +
      `<div class="note" style="margin-top:8px">対象 ${items.length}件 / 純利益 ${Math.round(totalProfit).toLocaleString()}円 / 正の寄与 ${Math.round(allPositive).toLocaleString()}円</div>`;
  }

  function drawHistogram() {
    const canvas = $("histogramChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    const detected = batchData.filter(item => item.detected && item.calendarDaysToStable != null);
    if (!detected.length) {
      drawEmpty(ctx,width,height,"底打ち候補を検出した銘柄がありません");
      return;
    }
    const bins = [
      {label:"0–6か月",min:0,max:183,count:0},
      {label:"6–12か月",min:184,max:365,count:0},
      {label:"1–2年",min:366,max:730,count:0},
      {label:"2–3年",min:731,max:1095,count:0},
      {label:"3–5年",min:1096,max:1825,count:0},
      {label:"5年以上",min:1826,max:Infinity,count:0}
    ];
    detected.forEach(item => {
      const bin = bins.find(candidate =>
        item.calendarDaysToStable >= candidate.min && item.calendarDaysToStable <= candidate.max);
      if (bin) bin.count++;
    });
    const left=46,top=25,right=width-16,bottom=height-48;
    const maxCount = Math.max(...bins.map(bin => bin.count),1);
    for (let i=0;i<=maxCount;i++) {
      const py = bottom - i*(bottom-top)/maxCount;
      ctx.strokeStyle="#e2e8f0"; ctx.setLineDash([2,4]);
      ctx.beginPath(); ctx.moveTo(left,py); ctx.lineTo(right,py); ctx.stroke();
      ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.textAlign="right"; ctx.textBaseline="middle"; ctx.fillText(String(i),left-8,py);
    }
    const slot=(right-left)/bins.length, barWidth=Math.min(70,slot*.62);
    bins.forEach((bin,index) => {
      const x=left+index*slot+(slot-barWidth)/2;
      const barHeight=bin.count*(bottom-top)/maxCount;
      const gradient=ctx.createLinearGradient(0,bottom-barHeight,0,bottom);
      gradient.addColorStop(0,"#2563eb"); gradient.addColorStop(1,"#60a5fa");
      ctx.fillStyle=gradient; ctx.fillRect(x,bottom-barHeight,barWidth,barHeight);
      ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="bottom";
      ctx.font='bold 12px "Yu Gothic UI",sans-serif';
      ctx.fillText(String(bin.count),x+barWidth/2,bottom-barHeight-5);
      ctx.fillStyle="#64748b"; ctx.textBaseline="top"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.fillText(bin.label,x+barWidth/2,bottom+10);
    });
    ctx.fillStyle="#475569"; ctx.font='bold 12px "Yu Gothic UI",sans-serif';
    ctx.textAlign="left"; ctx.textBaseline="top";
    ctx.fillText("上場日代理から底打ち候補確認までの分布",left,2);
  }

  function drawHistogram() {
    const canvas = $("histogramChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    const rankedItems = batchData.filter(item =>
      item.detected &&
      item.immediateBuyRank != null &&
      item.delayedBuyRank != null &&
      item.drawdownBuyRank != null
    );
    if (!rankedItems.length) {
      drawEmpty(ctx,width,height,"買い方ランキングを表示できる結果がありません");
      ctx.fillStyle="#64748b";
      ctx.font='12px "Yu Gothic UI",sans-serif';
      ctx.textAlign="center";
      ctx.fillText("遅延買付と下落待ち買付をONにして、底候補が検出された銘柄が対象です。",width/2,height/2+26);
      return;
    }
    const strategies = [
      {key:"immediateBuyRank", label:"底検知日", color:"#2563eb"},
      {key:"drawdownBuyRank", label:"下落待ち", color:"#059669"},
      {key:"delayedBuyRank", label:"遅延買い", color:"#d97706"},
    ];
    const counts = strategies.map(strategy => ({
      ...strategy,
      rank1: rankedItems.filter(item => Number(item[strategy.key]) === 1).length,
      rank2: rankedItems.filter(item => Number(item[strategy.key]) === 2).length,
      rank3: rankedItems.filter(item => Number(item[strategy.key]) === 3).length,
    }));
    const left=62,top=40,right=width-20,bottom=height-58;
    const maxCount = Math.max(
      ...counts.flatMap(item => [item.rank1,item.rank2,item.rank3]),
      1
    );
    const niceMax = Math.max(1, Math.ceil(maxCount / 5) * 5);
    for (let i=0;i<=5;i++) {
      const value = Math.round(niceMax * i / 5);
      const py = bottom - value*(bottom-top)/niceMax;
      ctx.strokeStyle="#e2e8f0"; ctx.setLineDash([2,4]);
      ctx.beginPath(); ctx.moveTo(left,py); ctx.lineTo(right,py); ctx.stroke();
      ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.textAlign="right"; ctx.textBaseline="middle"; ctx.fillText(String(value),left-8,py);
    }
    ctx.setLineDash([]);
    const groupWidth=(right-left)/counts.length;
    const barWidth=Math.min(34, groupWidth/5);
    const rankDefs = [
      {field:"rank1", label:"1位", alpha:1},
      {field:"rank2", label:"2位", alpha:.66},
      {field:"rank3", label:"3位", alpha:.34},
    ];
    counts.forEach((strategy,index) => {
      const groupX = left + index*groupWidth;
      rankDefs.forEach((rank,rankIndex) => {
        const value = strategy[rank.field];
        const x = groupX + groupWidth/2 - barWidth*1.7 + rankIndex*barWidth*1.35;
        const barHeight = value*(bottom-top)/niceMax;
        ctx.globalAlpha = rank.alpha;
        ctx.fillStyle = strategy.color;
        ctx.fillRect(x,bottom-barHeight,barWidth,barHeight);
        ctx.globalAlpha = 1;
        ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="bottom";
        ctx.font='bold 11px "Yu Gothic UI",sans-serif';
        ctx.fillText(String(value),x+barWidth/2,bottom-barHeight-4);
        ctx.fillStyle="#64748b"; ctx.textBaseline="top"; ctx.font='10px "Yu Gothic UI",sans-serif';
        ctx.fillText(rank.label,x+barWidth/2,bottom+7);
      });
      ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="top";
      ctx.font='bold 12px "Yu Gothic UI",sans-serif';
      ctx.fillText(strategy.label,groupX+groupWidth/2,bottom+25);
    });
    ctx.fillStyle="#475569"; ctx.font='bold 13px "Yu Gothic UI",sans-serif';
    ctx.textAlign="left"; ctx.textBaseline="top";
    ctx.fillText("買い方ランキング集計（現在までのリターン順）",left,8);
    ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
    ctx.textAlign="right";
    ctx.fillText(`対象 ${rankedItems.length}件`,right,10);
  }

  function drawHistogram() {
    const canvas = $("histogramChart");
    const {ctx,width,height} = fitCanvas(canvas);
    ctx.clearRect(0,0,width,height);
    const filterInfo = chartBatchFilterInfo();
    const sourceData = filterInfo.items;
    const strategies = [
      {rankKey:"immediateBuyRank", returnKey:"holdingReturnPercent", label:"底検知日", color:"#2563eb"},
      {rankKey:"drawdownBuyRank", returnKey:"drawdownHoldingReturnPercent", label:"下落待ち", color:"#059669"},
      {rankKey:"delayedBuyRank", returnKey:"delayedHoldingReturnPercent", label:"遅延買い", color:"#d97706"},
    ];
    if (sourceData.some(item => item.benchmarkHoldingReturnPercent != null)) {
      strategies.push({rankKey:"benchmarkBuyRank", returnKey:"benchmarkHoldingReturnPercent", label:"オルカン相当", color:"#7c3aed"});
    }
    const rankedItems = sourceData.filter(item =>
      item.detected &&
      item.immediateBuyRank != null &&
      item.delayedBuyRank != null &&
      item.drawdownBuyRank != null
    );
    const returnItems = sourceData.filter(item => item.detected && item.holdingReturnPercent != null);
    if (!rankedItems.length && !returnItems.length) {
      drawEmpty(ctx,width,height,"買い方比較を表示できる結果がありません");
      ctx.fillStyle="#64748b";
      ctx.font='12px "Yu Gothic UI",sans-serif';
      ctx.textAlign="center";
      ctx.fillText("まとめて分析後、底候補が検出された銘柄が対象です。",width/2,height/2+26);
      return;
    }

    const topArea = {left:62, top:36, right:width-20, bottom:Math.round(height*0.49)};
    const bottomArea = {left:62, top:Math.round(height*0.62), right:width-20, bottom:height-42};

    function drawRankingPanel() {
      if (!rankedItems.length) {
        ctx.fillStyle="#64748b";
        ctx.font='12px "Yu Gothic UI",sans-serif';
        ctx.textAlign="center";
        ctx.fillText("ランキング対象なし", (topArea.left+topArea.right)/2, (topArea.top+topArea.bottom)/2);
        return;
      }
      const counts = strategies.map(strategy => ({
        ...strategy,
        rank1: rankedItems.filter(item => Number(item[strategy.rankKey]) === 1).length,
        rank2: rankedItems.filter(item => Number(item[strategy.rankKey]) === 2).length,
        rank3: rankedItems.filter(item => Number(item[strategy.rankKey]) === 3).length,
        rank4: rankedItems.filter(item => Number(item[strategy.rankKey]) === 4).length,
      }));
      const maxCount = Math.max(...counts.flatMap(item => [item.rank1,item.rank2,item.rank3,item.rank4]),1);
      const niceMax = Math.max(1, Math.ceil(maxCount / 5) * 5);
      for (let i=0;i<=4;i++) {
        const value = Math.round(niceMax * i / 4);
        const py = topArea.bottom - value*(topArea.bottom-topArea.top)/niceMax;
        ctx.strokeStyle="#e2e8f0"; ctx.setLineDash([2,4]);
        ctx.beginPath(); ctx.moveTo(topArea.left,py); ctx.lineTo(topArea.right,py); ctx.stroke();
        ctx.fillStyle="#64748b"; ctx.font='10px "Yu Gothic UI",sans-serif';
        ctx.textAlign="right"; ctx.textBaseline="middle"; ctx.fillText(String(value),topArea.left-8,py);
      }
      ctx.setLineDash([]);
      const groupWidth=(topArea.right-topArea.left)/counts.length;
      const barWidth=Math.min(22, groupWidth/6);
      const rankDefs = [
        {field:"rank1", label:"1位", alpha:1},
        {field:"rank2", label:"2位", alpha:.66},
        {field:"rank3", label:"3位", alpha:.34},
        {field:"rank4", label:"4位", alpha:.18},
      ].slice(0, strategies.length);
      counts.forEach((strategy,index) => {
        const groupX = topArea.left + index*groupWidth;
        rankDefs.forEach((rank,rankIndex) => {
          const value = strategy[rank.field];
          const spacing = barWidth * 1.35;
          const x = groupX + groupWidth/2 - ((rankDefs.length - 1) * spacing + barWidth) / 2 + rankIndex * spacing;
          const barHeight = value*(topArea.bottom-topArea.top)/niceMax;
          ctx.globalAlpha = rank.alpha;
          ctx.fillStyle = strategy.color;
          ctx.fillRect(x,topArea.bottom-barHeight,barWidth,barHeight);
          ctx.globalAlpha = 1;
          ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="bottom";
          ctx.font='bold 10px "Yu Gothic UI",sans-serif';
          ctx.fillText(String(value),x+barWidth/2,topArea.bottom-barHeight-3);
          ctx.fillStyle="#64748b"; ctx.textBaseline="top"; ctx.font='9px "Yu Gothic UI",sans-serif';
          ctx.fillText(rank.label,x+barWidth/2,topArea.bottom+5);
        });
        ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="top";
        ctx.font='bold 11px "Yu Gothic UI",sans-serif';
        ctx.fillText(strategy.label,groupX+groupWidth/2,topArea.bottom+21);
      });
      ctx.fillStyle="#475569"; ctx.font='bold 13px "Yu Gothic UI",sans-serif';
      ctx.textAlign="left"; ctx.textBaseline="top";
      ctx.fillText("買い方ランキング集計",topArea.left,8);
      ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.textAlign="right";
      ctx.fillText(`順位対象 ${rankedItems.length}件`,topArea.right,10);
      ctx.textAlign="left";
      ctx.fillStyle="#64748b";
      ctx.font='10px "Yu Gothic UI",sans-serif';
      const filterLabel = filterInfo.settings.enabled
        ? `検出${filterInfo.rawDetected}件 → 直近${filterInfo.settings.years}年 ${filterInfo.dateFilteredDetected}件 → 集計${filterInfo.uniqueDetected}件`
        : `検出${filterInfo.rawDetected}件 → 集計${filterInfo.uniqueDetected}件`;
      ctx.fillText(filterLabel,topArea.left,24);
    }

    function investmentValue(item, strategy) {
      if (strategy.returnKey === "drawdownHoldingReturnPercent" && item.drawdownHoldingReturnPercent == null) {
        return 100;
      }
      const value = Number(item[strategy.returnKey]);
      if (!Number.isFinite(value)) return 100;
      return 100 * (1 + value / 100);
    }

    function drawReturnPanel() {
      if (!returnItems.length) return;
      const totals = strategies.map(strategy => ({
        ...strategy,
        total: returnItems.reduce((sum,item) => sum + investmentValue(item,strategy), 0),
      }));
      const baseTotal = returnItems.length * 100;
      const maxValue = Math.max(...totals.map(item => item.total), baseTotal, 1);
      const niceMax = Math.max(100, Math.ceil(maxValue / 500) * 500);
      for (let i=0;i<=4;i++) {
        const value = Math.round(niceMax * i / 4);
        const py = bottomArea.bottom - value*(bottomArea.bottom-bottomArea.top)/niceMax;
        ctx.strokeStyle="#e2e8f0"; ctx.setLineDash([2,4]);
        ctx.beginPath(); ctx.moveTo(bottomArea.left,py); ctx.lineTo(bottomArea.right,py); ctx.stroke();
        ctx.fillStyle="#64748b"; ctx.font='10px "Yu Gothic UI",sans-serif';
        ctx.textAlign="right"; ctx.textBaseline="middle"; ctx.fillText(String(value),bottomArea.left-8,py);
      }
      const baseY = bottomArea.bottom - baseTotal*(bottomArea.bottom-bottomArea.top)/niceMax;
      ctx.strokeStyle="#94a3b8"; ctx.setLineDash([5,4]);
      ctx.beginPath(); ctx.moveTo(bottomArea.left,baseY); ctx.lineTo(bottomArea.right,baseY); ctx.stroke();
      ctx.setLineDash([]);
      ctx.fillStyle="#64748b"; ctx.font='10px "Yu Gothic UI",sans-serif';
      ctx.textAlign="left"; ctx.fillText(`元本 ${baseTotal.toLocaleString()}円`,bottomArea.left+4,baseY-4);
      const slot=(bottomArea.right-bottomArea.left)/totals.length;
      const barWidth=Math.min(72,slot*.46);
      totals.forEach((strategy,index) => {
        const x=bottomArea.left+index*slot+(slot-barWidth)/2;
        const barHeight=strategy.total*(bottomArea.bottom-bottomArea.top)/niceMax;
        const gradient=ctx.createLinearGradient(0,bottomArea.bottom-barHeight,0,bottomArea.bottom);
        gradient.addColorStop(0,strategy.color);
        gradient.addColorStop(1,"#bfdbfe");
        ctx.fillStyle=gradient;
        ctx.fillRect(x,bottomArea.bottom-barHeight,barWidth,barHeight);
        ctx.fillStyle="#172033"; ctx.textAlign="center"; ctx.textBaseline="bottom";
        ctx.font='bold 11px "Yu Gothic UI",sans-serif';
        ctx.fillText(`${Math.round(strategy.total).toLocaleString()}円`,x+barWidth/2,bottomArea.bottom-barHeight-4);
        ctx.fillStyle="#64748b"; ctx.textBaseline="top"; ctx.font='bold 11px "Yu Gothic UI",sans-serif';
        ctx.fillText(strategy.label,x+barWidth/2,bottomArea.bottom+8);
      });
      ctx.fillStyle="#475569"; ctx.font='bold 13px "Yu Gothic UI",sans-serif';
      ctx.textAlign="left"; ctx.textBaseline="top";
      ctx.fillText("100円ずつ買った場合の合計評価額",bottomArea.left,bottomArea.top-25);
      ctx.fillStyle="#64748b"; ctx.font='11px "Yu Gothic UI",sans-serif';
      ctx.textAlign="right";
      ctx.fillText(`投資対象 ${returnItems.length}件・未約定は100円`,bottomArea.right,bottomArea.top-23);
      if (filterInfo.settings.enabled && (filterInfo.excludedByDate > 0 || filterInfo.duplicatesRemoved > 0)) {
        ctx.fillStyle="#94a3b8";
        ctx.font='10px "Yu Gothic UI",sans-serif';
        ctx.textAlign="right";
        ctx.fillText(`直近年数フィルター除外 ${filterInfo.excludedByDate}件 / 重複除外 ${filterInfo.duplicatesRemoved}件`,bottomArea.right,bottomArea.top-10);
      }
    }

    drawRankingPanel();
    drawReturnPanel();
    drawContributionBreakdown();
  }

  function handlePriceHover(event) {
    const found = nearestChartItem(chartViews.price, event);
    if (!found) { hideTooltip(); return; }
    const item = found.item;
    showTooltip(event,
      `<strong>${item.date}</strong><br>` +
      `終値：${money(item.close, stockData.currency)}`
    );
  }

  function handleStabilityHover(event) {
    const found = nearestChartItem(chartViews.stability, event);
    if (!found) { hideTooltip(); return; }
    const item = found.item;
    const tags = [];
    if (item.eligible) tags.push("底練り候補");
    if (item.peakOverheat) tags.push("過熱");
    if (item.peakCandidate) tags.push("ピーク強警戒");
    if (item.priceTrigger) tags.push("価格トリガー");
    showTooltip(event,
      `<strong>${item.date}</strong><br>` +
      `終値：${money(item.close, stockData.currency)}<br>` +
      `25日線：${item.ma25 == null ? "—" : money(item.ma25, stockData.currency)}<br>` +
      `75日線：${item.ma75 == null ? "—" : money(item.ma75, stockData.currency)}<br>` +
      `底スコア：${item.score == null ? "—" : item.score}<br>` +
      `ピークスコア：${item.peakScore == null ? "—" : item.peakScore}<br>` +
      `${tags.length ? "状態：" + tags.join(" / ") : ""}`
    );
  }

  function handlePriceHoverWithEvents(event) {
    const found = nearestChartItem(chartViews.price, event);
    if (!found) { hideTooltip(); return; }
    const item = found.item;
    showTooltip(event,
      `<strong>${item.date}</strong><br>` +
      `終値：${money(item.close, stockData.currency)}` +
      eventTooltipHtml(item.date)
    );
  }

  function handleStabilityHoverWithEvents(event) {
    const found = nearestChartItem(chartViews.stability, event);
    if (!found) { hideTooltip(); return; }
    const item = found.item;
    const tags = [];
    if (item.eligible) tags.push("底練り候補");
    if (item.peakOverheat) tags.push("過熱");
    if (item.peakCandidate) tags.push("ピーク強警戒");
    if (item.priceTrigger) tags.push("価格トリガー");
    const eventTags = chartEvents(chartViews.stability.data, chartViews.stability.events || [])
      .filter(event => event.index === found.index);
    if (eventTags.length) tags.push(eventTags.some(event => event.material) ? "材料確認ゾーン" : "重要開示日");
    showTooltip(event,
      `<strong>${item.date}</strong><br>` +
      `終値：${money(item.close, stockData.currency)}<br>` +
      `25日線：${item.ma25 == null ? "—" : money(item.ma25, stockData.currency)}<br>` +
      `75日線：${item.ma75 == null ? "—" : money(item.ma75, stockData.currency)}<br>` +
      `底スコア：${item.score == null ? "—" : item.score}<br>` +
      `ピークスコア：${item.peakScore == null ? "—" : item.peakScore}<br>` +
      `${tags.length ? "状態：" + tags.join(" / ") : ""}` +
      eventTooltipHtml(item.date)
    );
  }

  function finishSearchProgress(success = true) {
    if (searchProgressTimer) {
      clearInterval(searchProgressTimer);
      searchProgressTimer = null;
    }
    setSearchProgress(success ? 100 : searchProgressValue, success ? "検索完了" : "停止");
    setTimeout(() => {
      if (!searchProgressTimer) $("searchProgress").classList.add("hidden");
      if (!searchProgressTimer && $("topSearchProgress")) $("topSearchProgress").classList.add("hidden");
    }, success ? 350 : 1600);
  }

  function startEventProgress() {
    if (eventProgressTimer) clearInterval(eventProgressTimer);
    setEventProgress(4, "外部取得");
    eventProgressTimer = setInterval(() => {
      const next = eventProgressValue < 45
        ? eventProgressValue + 3
        : eventProgressValue < 78
          ? eventProgressValue + 2
          : eventProgressValue < 95
            ? eventProgressValue + 1
            : eventProgressValue;
      setEventProgress(next, next < 50 ? "外部確認" : next < 85 ? "保存中" : "外部取得待ち");
    }, 420);
  }

  function finishEventProgress(success = true) {
    if (eventProgressTimer) {
      clearInterval(eventProgressTimer);
      eventProgressTimer = null;
    }
    setEventProgress(success ? 100 : eventProgressValue, success ? "開示取得完了" : "停止");
    setTimeout(() => {
      if (!eventProgressTimer) $("eventProgress").classList.add("hidden");
    }, success ? 1100 : 1800);
  }

  $("search").addEventListener("click",searchStock);
  $("symbol").addEventListener("keydown",event => { if (event.key === "Enter") searchStock(); });
  $("showImportantEvents").addEventListener("change",event => {
    showImportantEvents = event.target.checked;
    updateImportantEventStatus(false);
    drawPriceChart();
    drawStabilityChart();
  });
  $("fetchImportantEvents").addEventListener("click",fetchImportantEventsForCurrentStock);
  $("priceChart").addEventListener("mousemove",handlePriceHoverWithEvents);
  $("priceChart").addEventListener("mouseleave",hideTooltip);
  $("stabilityChart").addEventListener("mousemove",handleStabilityHoverWithEvents);
  $("stabilityChart").addEventListener("mouseleave",hideTooltip);
  ["analysisStart","analysisEnd"].forEach(id => {
    $(id).addEventListener("input", event => sanitizeDateInput(event.target));
    $(id).addEventListener("blur", event => sanitizeDateInput(event.target));
  });
  $("clearAnalysisRange").addEventListener("click",() => {
    $("analysisStart").value = "";
    $("analysisEnd").value = "";
  });
  $("enableDelayedBuy").addEventListener("change",syncSimulationControls);
  $("enableDrawdownBuy").addEventListener("change",syncSimulationControls);
  $("chartRecentYears").addEventListener("input",drawHistogram);
  $("showContributionBreakdown").addEventListener("change",drawContributionBreakdown);
  $("contributionTopN").addEventListener("input",drawContributionBreakdown);
  async function runSymbolSearch() {
    const keyword = $("symbolSearch").value.trim();
    const box = $("symbolSearchResults");
    if (!keyword) {
      box.classList.add("hidden");
      box.innerHTML = "";
      return;
    }
    try {
      const response = await fetch("/api/symbol-search?q=" + encodeURIComponent(keyword));
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "検索できませんでした。");
      const results = body.results || [];
      if (!results.length) {
        box.innerHTML = '<div class="search-result"><span>候補がありません</span></div>';
      } else {
        box.innerHTML = results.map(item =>
          `<button class="search-result" type="button" data-symbol="${escapeHtml(item.symbol)}">
            <span><strong>${escapeHtml(item.symbol)}</strong><br><small>${escapeHtml(item.name)}</small></span>
            <small>${escapeHtml(item.market || "")}</small>
          </button>`
        ).join("");
        box.querySelectorAll("button").forEach(button => button.addEventListener("click",() => {
          $("symbol").value = button.dataset.symbol;
          $("market").value = "auto";
          box.classList.add("hidden");
          searchStock();
        }));
      }
      box.classList.remove("hidden");
    } catch (error) {
      box.innerHTML = `<div class="search-result"><span>${escapeHtml(error.message)}</span></div>`;
      box.classList.remove("hidden");
    }
  }
  async function runSymbolSearch() {
    const keyword = $("symbolSearch").value.trim();
    const box = $("symbolSearchResults");
    await renderSymbolCandidates(keyword, box);
  }

  async function renderSymbolCandidates(keyword, box) {
    if (!keyword) {
      box.classList.add("hidden");
      box.innerHTML = "";
      return;
    }
    try {
      const response = await fetch("/api/symbol-search?q=" + encodeURIComponent(keyword));
      const body = await response.json();
      if (!response.ok) throw new Error(body.error || "検索できませんでした。");
      const results = body.results || [];
      if (!results.length) {
        box.innerHTML = '<div class="search-result"><span>候補がありません</span></div>';
      } else {
        box.innerHTML = results.map(item => {
          const saved = item.saved ? "保存済み" : (item.source === "direct" ? "直接入力" : "");
          const badge = saved ? `<small style="color:#059669">${escapeHtml(saved)}</small>` : "";
          return `<button class="search-result" type="button" data-symbol="${escapeHtml(item.symbol)}">
            <span><strong>${escapeHtml(item.symbol)}</strong> ${badge}<br><small>${escapeHtml(item.name)}</small></span>
            <small>${escapeHtml(item.market || "")}</small>
          </button>`;
        }).join("");
        box.querySelectorAll("button").forEach(button => button.addEventListener("click",() => {
          $("symbol").value = button.dataset.symbol;
          $("symbolSearch").value = button.dataset.symbol;
          $("market").value = "auto";
          box.classList.add("hidden");
          searchStock();
        }));
      }
      box.classList.remove("hidden");
    } catch (error) {
      box.innerHTML = `<div class="search-result"><span>${escapeHtml(error.message)}</span></div>`;
      box.classList.remove("hidden");
    }
  }

  let symbolInputSearchTimer = null;
  $("symbol").addEventListener("input",() => {
    const keyword = $("symbol").value.trim();
    clearTimeout(symbolInputSearchTimer);
    symbolInputSearchTimer = setTimeout(() => {
      $("symbolSearch").value = keyword;
      renderSymbolCandidates(keyword, $("symbolSearchResults"));
    }, 180);
  });
  $("symbolSearchButton").addEventListener("click",runSymbolSearch);
  $("symbolSearch").addEventListener("keydown",event => { if (event.key === "Enter") runSymbolSearch(); });
  document.querySelectorAll(".chip").forEach(button => button.addEventListener("click",() => {
    $("symbol").value=button.dataset.symbol; $("market").value="auto"; searchStock();
  }));
  $("batchAnalyze").addEventListener("click",() => analyzeBatch());
  $("batchMarketCapAnalyze").addEventListener("click",() =>
    analyzeBatch({sortByMarketCap:true, runUntilLimit:true}));
  $("batchCancel").addEventListener("click",cancelBatch);
  $("batchCsv").addEventListener("click",exportBatchCsv);
  $("batchColumnsBasic").addEventListener("click",() => setBatchColumns("basic"));
  $("batchColumnsAll").addEventListener("click",() => setBatchColumns("all"));
  $("cacheUpdate").addEventListener("click",() =>
    runCacheAction("/api/cache/update","未確定銘柄の不足日足を追加取得しています…"));
  $("cacheAnalyzeMissing").addEventListener("click",() =>
    runCacheAction("/api/cache/reanalyze?mode=missing","未分析の保存銘柄を計算しています…"));
  $("cacheReanalyze").addEventListener("click",() =>
    runCacheAction("/api/cache/reanalyze?mode=all","保存済み日足から全銘柄を再計算しています…"));
  $("cacheShow").addEventListener("click",showCachedResults);
  $("marketCapCsvImport").addEventListener("click",() => $("marketCapCsvFile").click());
  $("marketCapCsvFile").addEventListener("change",event =>
    importMarketCapCsvFile(event.target.files && event.target.files[0]));
  $("quit").addEventListener("click",async () => {
    if (!confirm("株価分析アプリを終了しますか？")) return;
    try { await fetch("/shutdown",{method:"POST"}); } catch (_) {}
    document.body.innerHTML='<main class="app"><h1>アプリを終了しました</h1><p class="subtitle">このタブを閉じてください。</p></main>';
  });
  let resizeTimer = null;
  window.addEventListener("resize", () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      drawPriceChart();
      if (!$("stabilityPanel").classList.contains("hidden")) drawStabilityChart();
      drawHistogram();
    }, 120);
  });
  drawPriceChart();
  drawHistogram();
  renderBatchColumnPicker();
  syncSimulationControls();
  refreshCacheStatus();
  $("symbol").focus();
</script>
</body>
</html>
"""


class StockAppHandler(BaseHTTPRequestHandler):
    def log_message(self, _format: str, *_args: object) -> None:
        return

    def send_bytes(
        self, body: bytes, content_type: str, status: int = 200
    ) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, data: dict, status: int = 200) -> None:
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_bytes(body, "application/json; charset=utf-8", status)

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/":
            self.send_bytes(HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
            return

        if parsed.path == "/api/stock":
            query = parse_qs(parsed.query)
            raw_symbol = query.get("symbol", [""])[0]
            market = query.get("market", ["auto"])[0]
            period = query.get("period", ["1y"])[0]
            security_type = query.get("securityType", ["stock"])[0]
            analysis_start = query.get("analysisStart", [""])[0]
            analysis_end = query.get("analysisEnd", [""])[0]
            algorithm_mode = query.get("algorithmMode", ["general"])[0]
            delayed_buy_days = query.get(
                "delayedBuyDays", [str(DEFAULT_DELAYED_BUY_DAYS)]
            )[0]
            delayed_buy_enabled = request_bool(
                query.get("enableDelayedBuy", ["true"])[0],
                True,
            )
            drawdown_buy_percent = query.get(
                "drawdownBuyPercent", [str(DEFAULT_DRAWDOWN_BUY_PERCENT)]
            )[0]
            drawdown_buy_enabled = request_bool(
                query.get("enableDrawdownBuy", ["true"])[0],
                True,
            )
            drawdown_miss_zero_enabled = request_bool(
                query.get("drawdownMissZero", ["false"])[0],
                False,
            )
            try:
                symbol = normalize_symbol(raw_symbol, market)
                payload = build_stock_payload(
                    symbol,
                    period,
                    security_type,
                    analysis_start,
                    analysis_end,
                    algorithm_mode,
                    normalize_delayed_buy_days(delayed_buy_days),
                    delayed_buy_enabled,
                    normalize_drawdown_buy_percent(drawdown_buy_percent),
                    drawdown_buy_enabled,
                    drawdown_miss_zero_enabled,
                )
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            else:
                self.send_json(payload)
            return

        if parsed.path == "/api/cache/status":
            try:
                self.send_json(cache_status())
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/cache/results":
            try:
                self.send_json({"results": cached_analysis_results()})
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/symbol-search":
            try:
                query = parse_qs(parsed.query)
                keyword = query.get("q", [""])[0]
                self.send_json({"results": search_symbols(keyword)})
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/batch/status":
            try:
                query = parse_qs(parsed.query)
                job_id = query.get("jobId", [""])[0]
                self.send_json(get_batch_job(job_id))
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        self.send_json({"error": "ページが見つかりません。"}, 404)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/shutdown":
            self.send_json({"ok": True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()
            return

        if parsed.path == "/api/cache/update":
            try:
                self.send_json(update_all_cached_symbols())
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/cache/reanalyze":
            try:
                query = parse_qs(parsed.query)
                mode = query.get("mode", ["missing"])[0]
                if mode not in {"missing", "all"}:
                    raise ValueError("再計算モードが正しくありません。")
                self.send_json(
                    reanalyze_cached_symbols(only_missing=mode == "missing")
                )
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/market-cap/import":
            try:
                content_length = min(
                    int(self.headers.get("Content-Length", "0")),
                    20_000_000,
                )
                body = json.loads(self.rfile.read(content_length) or b"{}")
                csv_text = str(body.get("csvText", ""))
                self.send_json(import_market_cap_csv(csv_text))
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/batch":
            try:
                content_length = min(
                    int(self.headers.get("Content-Length", "0")), 20000
                )
                body = json.loads(self.rfile.read(content_length) or b"{}")
                raw_text = str(body.get("symbols", ""))
                mode = str(body.get("mode", "general"))
                sort_by_market_cap = bool(body.get("sortByMarketCap", False))
                run_until_limit = bool(body.get("runUntilLimit", False))
                universe = str(body.get("universe", "manual"))
                delayed_buy_days = normalize_delayed_buy_days(
                    body.get("delayedBuyDays", DEFAULT_DELAYED_BUY_DAYS)
                )
                delayed_buy_enabled = request_bool(
                    body.get("enableDelayedBuy", True),
                    True,
                )
                drawdown_buy_percent = normalize_drawdown_buy_percent(
                    body.get("drawdownBuyPercent", DEFAULT_DRAWDOWN_BUY_PERCENT)
                )
                drawdown_buy_enabled = request_bool(
                    body.get("enableDrawdownBuy", True),
                    True,
                )
                drawdown_miss_zero_enabled = request_bool(
                    body.get("drawdownMissZero", False),
                    False,
                )
                disable_saved_analysis_reuse = request_bool(
                    body.get("disableSavedAnalysisReuse", False),
                    False,
                )
                self.send_json(
                    start_batch_job(
                        raw_text,
                        mode,
                        sort_by_market_cap=sort_by_market_cap,
                        run_until_limit=run_until_limit,
                        universe=universe,
                        delayed_buy_days=delayed_buy_days,
                        delayed_buy_enabled=delayed_buy_enabled,
                        drawdown_buy_percent=drawdown_buy_percent,
                        drawdown_buy_enabled=drawdown_buy_enabled,
                        drawdown_miss_zero_enabled=drawdown_miss_zero_enabled,
                        disable_saved_analysis_reuse=disable_saved_analysis_reuse,
                    )
                )
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/batch/cancel":
            try:
                content_length = min(
                    int(self.headers.get("Content-Length", "0")), 2000
                )
                body = json.loads(self.rfile.read(content_length) or b"{}")
                self.send_json(request_batch_cancel(str(body.get("jobId", ""))))
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        if parsed.path == "/api/important-events/fetch":
            try:
                content_length = min(
                    int(self.headers.get("Content-Length", "0")), 4000
                )
                body = json.loads(self.rfile.read(content_length) or b"{}")
                symbol = str(body.get("symbol", "")).strip()
                if not symbol:
                    raise ValueError("銘柄コードがありません。")
                self.send_json(
                    fetch_important_events_payload(
                        symbol,
                        str(body.get("displayStart", "") or "") or None,
                        str(body.get("displayEnd", "") or "") or None,
                    )
                )
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return

        self.send_json({"error": "ページが見つかりません。"}, 404)
        if parsed.path == "/api/important-events/fetch":
            try:
                content_length = min(
                    int(self.headers.get("Content-Length", "0")), 4000
                )
                body = json.loads(self.rfile.read(content_length) or b"{}")
                symbol = str(body.get("symbol", "")).strip()
                if not symbol:
                    raise ValueError("銘柄コードがありません。")
                self.send_json(
                    fetch_important_events_payload(
                        symbol,
                        str(body.get("displayStart", "") or "") or None,
                        str(body.get("displayEnd", "") or "") or None,
                    )
                )
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
            return


def create_server() -> ThreadingHTTPServer:
    last_error: OSError | None = None
    for port in range(START_PORT, START_PORT + 10):
        try:
            return ThreadingHTTPServer((APP_HOST, port), StockAppHandler)
        except OSError as exc:
            last_error = exc
    raise OSError("アプリ用の通信ポートを確保できませんでした。") from last_error


def main() -> None:
    initialize_database()
    server = create_server()
    host, port = server.server_address
    url = f"http://{host}:{port}/"
    print(f"株価・底練り分析アプリを起動しました: {url}")
    print("終了するには画面の「アプリを終了」を押すか、Ctrl+Cを押してください。")
    if "--no-browser" not in sys.argv:
        threading.Timer(0.7, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
