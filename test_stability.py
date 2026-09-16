"""安定期判定アルゴリズムの回帰テスト。"""

import math
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest import mock

import app
from app import (
    PricePoint,
    StockResult,
    analyze_stability,
    analyze_bottoming,
    bottom_signal_evaluations,
    fetch_manual_analysis_points,
    search_symbols,
    slice_points_by_date,
)


def make_test_points(price_offset: float = 0.0) -> list[PricePoint]:
    points: list[PricePoint] = []
    for index in range(260):
        if index < 45:
            price = 200 - (110 * index / 44) + 5 * math.sin(index * 1.4)
        elif index < 180:
            price = (
                84
                + 2.2 * math.sin(index / 8)
                + 0.8 * math.sin(index / 2.7)
            )
        elif index == 180:
            price = 93
        elif index == 181:
            price = 95
        elif index == 182:
            price = 96
        else:
            price = (
                96
                + (index - 182) * 0.24
                + 1.8 * math.sin(index / 9)
            )
        price += price_offset
        spread = 0.018 if index >= 45 else 0.055
        volume = 4_000_000 if index == 180 else 1_000_000
        if index == 180:
            high = price * 1.004
            low = price * 0.90
        else:
            high = price * (1 + spread / 2)
            low = price * (1 - spread / 2)
        points.append(
            PricePoint(
                timestamp=1_577_836_800 + index * 86_400,
                date_text=f"day-{index:03d}",
                close=price,
                high=high,
                low=low,
                volume=volume,
            )
        )
    return points


def make_recovered_ipo_points() -> list[PricePoint]:
    points: list[PricePoint] = []
    for index in range(210):
        if index < 25:
            price = 100 + index * 4
        elif index < 65:
            price = 200 - (110 * (index - 25) / 39)
        elif index < 160:
            price = 145 + 6 * math.sin(index / 7) + 2 * math.sin(index / 2.5)
        elif index == 160:
            price = 175
        elif index == 161:
            price = 184
        elif index == 162:
            price = 186
        else:
            price = 186 + (index - 162) * 0.6
        spread = 0.025 if index >= 65 else 0.06
        volume = 4_000_000 if index == 160 else 1_000_000
        if index == 160:
            high = price * 1.01
            low = price * 0.92
        else:
            high = price * (1 + spread / 2)
            low = price * (1 - spread / 2)
        points.append(
            PricePoint(
                timestamp=1_735_171_200 + index * 86_400,
                date_text=f"ipo-{index:03d}",
                close=price,
                high=high,
                low=low,
                volume=volume,
            )
        )
    return points


def make_peak_warning_points() -> list[PricePoint]:
    points: list[PricePoint] = []
    for index in range(230):
        if index < 120:
            price = 100 + 2 * math.sin(index / 6)
        elif index < 190:
            price = 100 + (index - 120) * 2.5
        elif index < 205:
            price = 275 - (index - 190) * 3.5
        else:
            price = 222 + 3 * math.sin(index / 3)
        spread = 0.03 if index < 180 else 0.08
        points.append(
            PricePoint(
                timestamp=1_735_171_200 + index * 86_400,
                date_text=f"peak-{index:03d}",
                close=price,
                high=price * (1 + spread / 2),
                low=price * (1 - spread / 2),
                volume=1_000_000,
            )
        )
    return points


class StabilityAlgorithmTests(unittest.TestCase):
    def test_detects_confirmed_price_breakout(self) -> None:
        result = analyze_stability(make_test_points())

        self.assertTrue(result["detected"])
        self.assertEqual(result["stableDate"], "day-182")
        self.assertLessEqual(
            result["metricsAtStable"]["peakPriceRatio"],
            0.50,
        )
        self.assertEqual(
            result["metricsAtStable"]["triggerEventDate"],
            "day-180",
        )
        self.assertEqual(
            result["metricsAtStable"]["triggerType"],
            "volume_breakout_confirmed",
        )

    def test_rejects_high_price_breakout(self) -> None:
        result = analyze_stability(make_test_points(price_offset=200))

        self.assertFalse(result["detected"])
        self.assertEqual(result["priceTriggerCount"], 0)

    def test_can_switch_to_ipo_algorithm(self) -> None:
        result = analyze_bottoming(make_test_points(), mode="ipo")

        self.assertEqual(result["algorithmMode"], "ipo")
        self.assertIn("firstYearCalendarDays", result["config"])

    def test_ipo_algorithm_detects_recovered_bottom_breakout(self) -> None:
        result = analyze_bottoming(make_recovered_ipo_points(), mode="ipo")

        self.assertTrue(result["detected"])
        self.assertEqual(result["metricsAtStable"]["triggerEventDate"], "ipo-160")
        self.assertGreaterEqual(
            result["metricsAtStable"]["recentLowDrawdownPercent"], 50
        )

    def test_peak_warning_zone_is_colored_candidate(self) -> None:
        result = analyze_bottoming(make_peak_warning_points(), mode="general")

        self.assertGreater(result["peakWarningCount"], 0)
        self.assertTrue(
            any(row.get("peakCandidate") for row in result["series"])
        )

    def test_bottom_candidate_evaluation_compares_future_low(self) -> None:
        points = make_test_points()
        signals = [
            {
                "confirmationDate": "day-182",
                "confirmationClose": points[182].close,
                "triggerDate": "day-180",
                "triggerType": "volume_breakout_confirmed",
            }
        ]

        evaluations = bottom_signal_evaluations(signals, points)

        self.assertEqual(evaluations[0]["date"], "day-182")
        self.assertIn(evaluations[0]["verdict"], {"成功", "許容", "早すぎ"})
        self.assertIn("tradingDaysToMinAfter", evaluations[0])
        self.assertIn("previousPeakPrice", evaluations[0])
        self.assertIn("drawdownFromPreviousPeakPercent", evaluations[0])
        self.assertIn("bottomPositionRatio", evaluations[0])
        self.assertIn("maxBeforeActualBottomPrice", evaluations[0])
        self.assertIn("riseBeforeActualBottomPercent", evaluations[0])
        self.assertIn("holdingReturnPercent", evaluations[0])
        self.assertIn("annualizedReturnPercent", evaluations[0])
        self.assertIn("tradingDaysHeld", evaluations[0])
        app.add_holding_performance_to_evaluations(evaluations, points, 10)
        self.assertEqual(evaluations[0]["delayedBuyDays"], 10)
        self.assertIn("delayedBuyDate", evaluations[0])
        self.assertIn("delayedHoldingReturnPercent", evaluations[0])
        self.assertIn("delayedAnnualizedReturnPercent", evaluations[0])
        app.add_holding_performance_to_evaluations(evaluations, points, 10, True, -5)
        self.assertEqual(evaluations[0]["drawdownBuyPercent"], -5)
        self.assertIn("drawdownBuyTargetPrice", evaluations[0])
        self.assertIn("drawdownHoldingReturnPercent", evaluations[0])
        app.add_holding_performance_to_evaluations(
            evaluations,
            points,
            10,
            delayed_buy_enabled=False,
            drawdown_buy_enabled=False,
        )
        self.assertIsNone(evaluations[0]["delayedBuyDate"])
        self.assertIsNone(evaluations[0]["drawdownBuyDate"])

    def test_primary_bottom_evaluation_uses_latest_candidate(self) -> None:
        analysis = {
            "stableDate": "2020-01-01",
            "bottomEvaluations": [
                {"date": "2020-01-01", "verdict": "成功"},
                {"date": "2021-01-01", "verdict": "許容"},
            ],
        }

        self.assertEqual(
            app.primary_bottom_evaluation(analysis)["date"],
            "2021-01-01",
        )

    def test_rejects_breakout_that_immediately_collapses(self) -> None:
        points = make_test_points()[:183]
        points[181] = replace(
            points[181],
            close=80,
            high=82,
            low=78,
            volume=1_200_000,
        )
        points[182] = replace(
            points[182],
            close=79,
            high=81,
            low=77,
            volume=1_100_000,
        )

        result = analyze_stability(points)

        self.assertFalse(result["detected"])
        self.assertGreater(result["priceTriggerCount"], 0)

    def test_manual_date_range_limits_analysis_scope(self) -> None:
        points, scope = slice_points_by_date(
            make_test_points(),
            start_date="2020-01-01",
            end_date="2020-06-15",
        )

        result = analyze_stability(points, analysis_scope=scope)

        self.assertTrue(result["analysisScope"]["custom"])
        self.assertEqual(result["analysisScope"]["requestedEnd"], "2020-06-15")
        self.assertFalse(result["detected"])

    def test_manual_range_fetches_requested_dates(self) -> None:
        fetched_points = make_test_points()
        old_cached_points = fetched_points[:80]

        with mock.patch(
            "app.fetch_history_range", return_value=StockResult(
                symbol="TEST",
                name="Test Company",
                currency="JPY",
                exchange="Tokyo",
                points=fetched_points,
                first_trade_timestamp=fetched_points[0].timestamp,
            )
        ) as fetch_mock:
            points, scope = fetch_manual_analysis_points(
                "TEST",
                old_cached_points,
                start_date="2020-06-01",
                end_date="2020-08-01",
            )

        self.assertTrue(fetch_mock.called)
        self.assertGreater(len(points), 0)
        self.assertEqual(scope["requestedStart"], "2020-06-01")
        self.assertEqual(scope["requestedEnd"], "2020-08-01")


class CacheTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.original_database_path = app.DATABASE_PATH
        app.DATABASE_PATH = str(
            Path(self.temporary_directory.name) / "test_cache.db"
        )
        app.initialize_database()

    def tearDown(self) -> None:
        app.DATABASE_PATH = self.original_database_path
        self.temporary_directory.cleanup()

    def save_detected_test_stock(self) -> tuple[StockResult, dict]:
        points = make_test_points()
        result = StockResult(
            symbol="TEST",
            name="Test Company",
            currency="JPY",
            exchange="Tokyo",
            points=points,
            first_trade_timestamp=points[0].timestamp,
        )
        analysis = analyze_stability(points)
        app.save_history(result, history_complete=True)
        app.save_analysis(result.symbol, analysis)
        return result, analysis

    def test_saves_prices_without_duplicates(self) -> None:
        result, _analysis = self.save_detected_test_stock()
        app.save_history(result, history_complete=True)

        status = app.cache_status()
        self.assertEqual(status["stockCount"], 1)
        self.assertEqual(status["priceCount"], len(result.points))
        self.assertEqual(status["analysisCount"], 1)
        self.assertEqual(status["detectedCount"], 1)

    def test_symbol_search_finds_seed_symbol(self) -> None:
        results = search_symbols("メルカリ")

        self.assertTrue(any(item["symbol"] == "4385.T" for item in results))

    def test_normalize_alphanumeric_japanese_symbol(self) -> None:
        self.assertEqual(app.normalize_symbol("285A", "auto"), "285A.T")
        self.assertEqual(app.normalize_symbol("285A.T", "auto"), "285A.T")

    def test_batch_symbol_parser_has_no_old_15_symbol_limit(self) -> None:
        symbols = app.parse_batch_symbols("\n".join(str(1000 + i) for i in range(30)))

        self.assertEqual(len(symbols), 30)

    def test_market_cap_sorted_batch_symbols(self) -> None:
        with mock.patch(
            "app.fetch_market_caps",
            return_value={"7203.T": 10_000, "6758.T": 30_000, "AAPL": 20_000},
        ):
            symbols = app.market_cap_sorted_batch_symbols("7203 6758 AAPL")

        self.assertEqual(symbols, ["6758.T", "AAPL", "7203.T"])

    def test_market_cap_sort_uses_known_symbols_when_input_is_empty(self) -> None:
        with (
            mock.patch("app.all_known_batch_symbols", return_value=["7203.T", "AAPL"]),
            mock.patch("app.fetch_market_caps", return_value={"7203.T": 10_000, "AAPL": 20_000}),
        ):
            symbols, warning = app.market_cap_sorted_batch_symbols_with_warning("")

        self.assertEqual(symbols, ["AAPL", "7203.T"])
        self.assertIsNone(warning)

    def test_market_cap_sort_falls_back_when_quote_api_fails(self) -> None:
        with mock.patch(
            "app.fetch_market_caps",
            side_effect=app.StockDataError("http_error", "HTTP 401"),
        ):
            symbols, warning = app.market_cap_sorted_batch_symbols_with_warning(
                "7203 6758 AAPL"
            )

        self.assertEqual(symbols, ["7203", "6758", "AAPL"])
        self.assertIn("http_error", warning)

    def test_batch_result_includes_bottom_evaluation(self) -> None:
        result, analysis = self.save_detected_test_stock()

        batch_result = app.analyze_one_for_batch_with_update(
            result.symbol,
            update_missing=False,
        )

        self.assertEqual(batch_result["stableDate"], analysis["stableDate"])
        self.assertIn("drawdownAfterPercent", batch_result)
        self.assertIn("previousPeakPrice", batch_result)
        self.assertIn("drawdownFromPreviousPeakPercent", batch_result)
        self.assertIn("bottomPositionRatio", batch_result)
        self.assertIn("maxBeforeActualBottomPrice", batch_result)
        self.assertIn("riseBeforeActualBottomPercent", batch_result)
        self.assertIn("holdingReturnPercent", batch_result)
        self.assertIn("annualizedReturnPercent", batch_result)
        self.assertIn("tradingDaysHeld", batch_result)
        self.assertIn("delayedHoldingReturnPercent", batch_result)
        self.assertIn("delayedAnnualizedReturnPercent", batch_result)
        self.assertIn("drawdownHoldingReturnPercent", batch_result)
        self.assertIn("drawdownAnnualizedReturnPercent", batch_result)
        self.assertIn(batch_result["bottomVerdict"], {"成功", "許容", "早すぎ"})

    def test_batch_result_uses_custom_delayed_buy_days(self) -> None:
        result, _analysis = self.save_detected_test_stock()

        batch_result = app.analyze_one_for_batch_with_update(
            result.symbol,
            update_missing=False,
            delayed_buy_days=12,
        )

        self.assertEqual(batch_result["delayedBuyDays"], 12)
        self.assertIsNotNone(batch_result["delayedBuyDate"])

    def test_batch_result_uses_drawdown_buy_percent(self) -> None:
        result, _analysis = self.save_detected_test_stock()

        batch_result = app.analyze_one_for_batch_with_update(
            result.symbol,
            update_missing=False,
            drawdown_buy_percent=-5,
        )

        self.assertEqual(batch_result["drawdownBuyPercent"], -5)
        self.assertIsNotNone(batch_result["drawdownBuyTargetPrice"])

    def test_market_cap_estimate_falls_back_to_shares_outstanding(self) -> None:
        with mock.patch.object(app, "fetch_quote_summary", return_value={}), (
            mock.patch.object(
                app,
                "fetch_quote_detail_summary",
                return_value={
                    "price": {"currency": "JPY"},
                    "defaultKeyStatistics": {
                        "sharesOutstanding": {"raw": 1_000_000}
                    },
                },
            )
        ):
            bottom_cap, current_cap, currency = app.estimated_market_cap_at_price_jpy(
                "TEST.T",
                50,
                100,
                "JPY",
            )

        self.assertEqual(current_cap, 100_000_000)
        self.assertEqual(bottom_cap, 50_000_000)
        self.assertEqual(currency, "JPY")

    def test_market_cap_estimate_falls_back_to_yahoo_page_json(self) -> None:
        with mock.patch.object(app, "fetch_quote_summary", return_value={}), (
            mock.patch.object(app, "fetch_quote_detail_summary", return_value={})
        ), mock.patch.object(
            app,
            "request_text_url",
            return_value='{"marketCap":{"raw":200000000},"currency":"JPY"}',
        ):
            bottom_cap, current_cap, currency = app.estimated_market_cap_at_price_jpy(
                "TEST.T",
                25,
                100,
                "JPY",
            )

        self.assertEqual(current_cap, 200_000_000)
        self.assertEqual(bottom_cap, 50_000_000)
        self.assertEqual(currency, "JPY")

    def test_market_cap_estimate_falls_back_to_japanese_html(self) -> None:
        with mock.patch.object(app, "fetch_quote_summary", return_value={}), (
            mock.patch.object(app, "fetch_quote_detail_summary", return_value={})
        ), mock.patch.object(app, "fetch_market_cap_from_yahoo_page", return_value=(None, "")), (
            mock.patch.object(
                app,
                "request_text_url",
                return_value="時価総額 1兆2,345億円",
            )
        ):
            bottom_cap, current_cap, currency = app.estimated_market_cap_at_price_jpy(
                "7203.T",
                50,
                100,
                "JPY",
            )

        self.assertEqual(current_cap, 1_234_500_000_000)
        self.assertEqual(bottom_cap, 617_250_000_000)
        self.assertEqual(currency, "JPY")

    def test_market_cap_estimate_falls_back_to_cached_market_cap(self) -> None:
        points = make_test_points()
        result = StockResult(
            symbol="CACHE.T",
            name="Cache Corp",
            currency="JPY",
            exchange="Tokyo",
            points=points,
            first_trade_timestamp=points[0].timestamp,
        )
        app.save_history(result, history_complete=True, long_history_complete=True)
        app.save_stock_market_cap("CACHE.T", 300_000_000, "JPY")

        with mock.patch.object(app, "fetch_quote_summary", return_value={}), (
            mock.patch.object(app, "fetch_quote_detail_summary", return_value={})
        ), mock.patch.object(app, "fetch_market_cap_from_yahoo_page", return_value=(None, "")):
            bottom_cap, current_cap, currency = app.estimated_market_cap_at_price_jpy(
                "CACHE.T",
                50,
                100,
                "JPY",
            )

        self.assertEqual(current_cap, 300_000_000)
        self.assertEqual(bottom_cap, 150_000_000)
        self.assertEqual(currency, "JPY")

    def test_import_market_cap_csv_accepts_japanese_headers(self) -> None:
        outcome = app.import_market_cap_csv(
            "コード,時価総額（百万円）,単位\n"
            "7203,48000000,百万円\n"
            "6758,2兆5000億円,JPY\n"
        )

        self.assertEqual(outcome["imported"], 2)
        toyota_cap, toyota_currency = app.cached_stock_market_cap("7203.T")
        sony_cap, sony_currency = app.cached_stock_market_cap("6758.T")
        self.assertEqual(toyota_cap, 48_000_000_000_000)
        self.assertEqual(toyota_currency, "JPY")
        self.assertEqual(sony_cap, 2_500_000_000_000)
        self.assertEqual(sony_currency, "JPY")

    def test_batch_can_use_ipo_mode(self) -> None:
        points = make_recovered_ipo_points()
        result = StockResult(
            symbol="IPO",
            name="IPO Company",
            currency="JPY",
            exchange="Tokyo",
            points=points,
            first_trade_timestamp=points[0].timestamp,
        )
        app.save_history(result, history_complete=True)
        app.save_analysis(result.symbol, analyze_stability(points))

        batch_result = app.analyze_one_for_batch_with_update(
            result.symbol,
            mode="ipo",
            update_missing=False,
        )

        self.assertEqual(batch_result["algorithmMode"], "ipo")
        self.assertTrue(batch_result["detected"])

    def test_detected_stock_uses_cache_without_network(self) -> None:
        result, analysis = self.save_detected_test_stock()

        with mock.patch.object(
            app, "fetch_stock_data", side_effect=AssertionError("network")
        ), mock.patch.object(
            app, "fetch_history_range", side_effect=AssertionError("network")
        ):
            cached, loaded_analysis, changed = app.ensure_symbol_cache(
                result.symbol
            )

        self.assertFalse(changed)
        self.assertEqual(len(cached.points), len(result.points))
        self.assertEqual(
            loaded_analysis["stableDate"], analysis["stableDate"]
        )

    def test_batch_can_reuse_saved_analysis_without_recalculation(self) -> None:
        result, analysis = self.save_detected_test_stock()

        with mock.patch.object(
            app, "analyze_stability", side_effect=AssertionError("reanalyze")
        ):
            cached, loaded_analysis, changed = app.ensure_symbol_cache(
                result.symbol,
                update_missing=False,
                prefer_saved_analysis=True,
            )

        self.assertFalse(changed)
        self.assertEqual(cached.symbol, result.symbol)
        self.assertEqual(loaded_analysis["stableDate"], analysis["stableDate"])

    def test_reanalyzes_from_saved_prices(self) -> None:
        result, _analysis = self.save_detected_test_stock()
        with app.database_connection() as connection:
            connection.execute(
                "DELETE FROM analyses WHERE symbol = ?", (result.symbol,)
            )

        outcome = app.reanalyze_cached_symbols(only_missing=True)

        self.assertEqual(outcome["targetCount"], 1)
        self.assertEqual(outcome["completedCount"], 1)
        self.assertTrue(app.load_saved_analysis(result.symbol)["detected"])

    def test_incremental_update_adds_only_new_dates(self) -> None:
        points = make_test_points()[:110]
        result = StockResult(
            symbol="GROW",
            name="Growing Company",
            currency="JPY",
            exchange="Tokyo",
            points=points,
            first_trade_timestamp=points[0].timestamp,
        )
        app.save_history(result, history_complete=False)
        app.save_analysis(result.symbol, analyze_stability(points))

        incremental_points = make_test_points()[95:150]
        incremental = StockResult(
            symbol=result.symbol,
            name=result.name,
            currency=result.currency,
            exchange=result.exchange,
            points=incremental_points,
            first_trade_timestamp=result.first_trade_timestamp,
        )

        with mock.patch.object(
            app, "fetch_history_range", return_value=incremental
        ) as fetch_mock:
            cached, _analysis, changed = app.ensure_symbol_cache(
                result.symbol
            )

        self.assertTrue(changed)
        self.assertEqual(len(cached.points), 150)
        fetch_mock.assert_called_once()

    def test_complete_history_flag_never_moves_backwards(self) -> None:
        result, _analysis = self.save_detected_test_stock()
        app.save_history(result, history_complete=True)
        app.save_history(result, history_complete=False)

        row = app.stock_row(result.symbol)
        self.assertEqual(row["history_complete"], 1)


class ImportantEventTests(unittest.TestCase):
    @unittest.skip("literal Japanese in this file can be mojibaked in the local console path")
    def test_parse_tdnet_disclosures_extracts_earnings_event(self) -> None:
        html = """
        <tr>
          <td>2026/05/15</td><td>285A</td>
          <td><a href="/inbs/140120260515555555.pdf">2026年３月期 決算短信〔ＩＦＲＳ〕</a></td>
        </tr>
        """
        events = app.parse_tdnet_disclosures(html, "285A", "2026-05-15")
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0]["eventDate"], "2026-05-15")
        self.assertEqual(events[0]["category"], "決算")
        self.assertEqual(events[0]["source"], "TDnet")

    def test_parse_tdnet_disclosures_extracts_event_without_literal_japanese(self) -> None:
        title = "FY2026 " + app.IMPORTANT_DISCLOSURE_KEYWORDS[0]
        html = (
            '<tr><td>2026/05/15</td><td>285A</td>'
            '<td><a href="/inbs/140120260515555555.pdf">'
            + title
            + "</a></td></tr>"
        )
        events = app.parse_tdnet_disclosures(html, "285A", "2026-05-15")
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0]["eventDate"], "2026-05-15")
        self.assertEqual(events[0]["category"], app.disclosure_category(title))
        self.assertEqual(events[0]["source"], "TDnet")

    def test_important_event_annotation_marks_material_move(self) -> None:
        points = [
            PricePoint(1, "2026-05-14", 100, 101, 99, 1_000),
            PricePoint(2, "2026-05-15", 112, 115, 108, 5_000),
            PricePoint(3, "2026-05-18", 118, 120, 110, 3_000),
            PricePoint(4, "2026-05-19", 121, 122, 119, 2_000),
        ]
        events = [
            {
                "eventDate": "2026-05-15",
                "title": "決算短信",
                "category": "決算",
                "source": "TDnet",
                "url": "",
            }
        ]
        annotated = app.annotate_important_events(events, points)
        self.assertEqual(annotated[0]["chartDate"], "2026-05-15")
        self.assertTrue(annotated[0]["material"])
        self.assertAlmostEqual(annotated[0]["impactPercent"], 21.0)


if __name__ == "__main__":
    unittest.main()
