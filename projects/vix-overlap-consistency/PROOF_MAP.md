# Proof dependencies

The final build status is recorded in VERIFICATION.md. Every arrow below is an
import or proved implication, not an external-solver assumption.

| Obligation | Lean source and principal declaration |
|---|---|
| Finite laws, histories, positive SPX, martingale, diagonal, full tower | `Model.lean`: `FiniteLaw`, `HistoryFiltration`, `FiniteModel` |
| Additive integrated budgets at a fixed valuation date | `BudgetAlgebra.lean`: `intervalBudget_additive` |
| All 64 binary schedules and prefix/window counts | `ScheduleData.lean`: `Schedule`, `prefixCount`, `windowCount` |
| Independent fair signs and unnormalized conditioning | `CoinProduct.lean`: product and masked-average lemmas |
| Positive stock realization; stock distribution depends only on prefix count | `ScheduleStock.lean`: `stockValue_formula`, `uniform_stock_function_eq_of_prefixCount_eq` |
| Every real schedule law gives the same structural architecture | `ScheduleModel.lean`: `model` |
| Exact tenor, VIX normalization, full window conditional-log identity | `ScheduleModel.lean`: `window_tenor`, `model_vix`, `model_window_log_identity` |
| Nonvacuity with positive root variance budgets | `ScheduleModel.lean`: `uniform_model_nonzero` |
| Common pointwise stock/log/budget and moment bounds | `ScheduleBounds.lean`: `stockValue_bounds`, `stockValue_log_bound`, `budgetValue_le_c`, `uniform_moment_bound` |
| Unit forwards and expected SPX log increments | `ScheduleMoments.lean`: `model_stock_forward`, `model_expected_log_ratio`, `model_expected_window_log`, `model_overlap_log_cost` |
| Calls plus cash identify atoms, including a zero VIX atom | `Vanilla.lean`: `nonneg_calls_identify_fiber_statistic` |
| SPX support value identifies activity count by prime factorization | `PriceIdentification.lean`: `active_count_identified` |
| Ordinary-call calibration definitions | `QuoteContract.lean`: `Calibrates`, `ThreeWindowObstruction` |
| Exact witness tables and checked separator; arbitrary real weights | `ScheduleCertificate.lean`: `proper_panel_feasible`, `universal_separator`, `three_window_count_obstruction` |
| Counts follow from ordinary quotes; ordinary quotes follow from count witnesses | `QuoteBridge.lean`: `stock_calls_force_prefix`, `window_calls_force_marginal`, `vanilla_three_window_obstruction` |
| Frozen overlap tests at all strikes and second moments | `PairTests.lean`: `vix_squared_overlap`, `vix_squared_mean` |
| Tests tied to actual SPX log returns; exact positive margin | `FinancialTests.lean`: `quoted_second_moment_log_identity`, `quoted_overlap_log_inequality`, `exact_separation_margin` |
| Complete integrated theorem using actual structural model calls | `Headline.lean`: `financial_three_window_obstruction` |
| Exact statements and transitive axiom dependencies | `Audit.lean` |

The main chain is:

1. Construct `model p` for every real probability law `p` on all 64 schedules,
   using the fixed 4,096-state carrier and fixed information rules.
2. Derive stock/window count distributions from ordinary call prices. Neither
   schedules nor budgets are added to the observable quote panel.
3. Check the explicit pair witnesses and the pointwise integer separator in
   Lean; prove the implication for arbitrary real probabilities.
4. Lift witnesses and impossibility to actual `FiniteModel` calls, carrying the
   common root budgets, moment bound, conditional log identity, and frozen tests.

The numerical LP is used only to discover data. The JSON data generator writes
literal tables; ordinary `decide` checks finite integer facts in the kernel,
and algebraic proofs carry them to real expectations. No LP-duality theorem,
external certificate oracle, or continuous-realization theorem is assumed.
