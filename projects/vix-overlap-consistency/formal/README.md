# Lean infrastructure and structural model

This directory contains the finite filtered structural model, a fully proved
six-cell schedule-and-sign realization, and the exact quote-certificate
modules. The main integrated statement and its verification status are
recorded in the project's `THEOREM.md` and `VERIFICATION.md`.

The pinned compiler is Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. The pinned Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`).
`lake-manifest.json` records every transitive package revision. BrownianMotion
and formal-mathfin are not dependencies, and no continuous-realization result
is assumed.

From the repository root, run:

```sh
projects/vix-overlap-consistency/scripts/verify.sh
```

Set `VIX_LEAN=/absolute/path/to/lean` if Lean is not on PATH. On the research
Mac, the script also recognizes the already-installed compiler under the
repository's `.research-cache/toolchains`. It checks the exact compiler and
dependency revisions, refuses modified dependency sources, and recompiles every
local module in dependency order. Only one compiler runs at a time, with one
thread, process priority `nice 19`, and a 4,096 MB internal Lean allocation cap.
The allocation cap is a Lean runtime limit, not a measurement of physical
memory usage. Resource measurements must time the Lean executable directly:
`lake env lean` spawns a child, so the Lake wrapper's reported physical
footprint cannot be attributed to Lean. Missing Mathlib artifacts are obtained
for the selected imports only; it does not compile the whole library. An initial
dependency setup needs network access. The current local dependency cache was
copied using APFS copy-on-write from an existing task, never shared mutably.

`VixOverlap/Audit.lean` prints exact theorem statements and their axiom
dependencies. The build rejects proof placeholders, custom axiom declarations,
and native computation oracles in the local dependency closure. The only
allowed reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The checker itself is orchestration, not a proof oracle: each theorem body is
elaborated by Lean and its proof term is checked by the Lean kernel.

## Declaration audit

`Real.log` was inspected in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`. Mathlib extends it to
nonpositive arguments; `FiniteModel.stock_pos` prevents that extension from
being used for the stock-return relation. The diagonal row uses exactly
`-2 * Real.log (S_end / S_start)`.

`Real.sqrt`, `Real.sq_sqrt`, and `Real.sqrt_nonneg` were inspected in
`Mathlib/Analysis/Real/Sqrt.lean`. The square-root identity requires a
nonnegative argument. The local proof establishes this from nonnegative
budgets and strictly positive elapsed tenor, rather than assuming the desired
VIX-squared identity as a field.

All conditional rows use `historySum` and `historyMass`. They never divide by a
history probability. Partitions may refine by arbitrary information, and the
initial partition is indiscrete. The terminal partition is unrestricted.
`EventGrid`, `FiniteLaw`, `HistoryFiltration`, and `FiniteModel` do not by
themselves restrict supports to a solver grid or identify a quote-implied joint
law. A concrete finite-state architecture must be stated separately and proved
to satisfy this structure.

`structural_class_nonempty` establishes a supporting constant-stock example.
The stronger `ScheduleModel.model` constructs every schedule law on the same
4,096 labeled schedule/sign states. Its proof establishes positivity, adapted
prices and budgets, every martingale row, diagonal log-return rows, and all
full-history tower rows. `model_window_log_identity` proves the conditional
window log relation without dividing by a history mass.

`CoinProduct` proves the finite product/conditioning algebra used by this
construction. `ScheduleStock` proves the exact stock formula and proves that
its conditional sign-averaged distribution depends only on the number of
active cells. Neither proof enumerates conditional histories.
`ScheduleModel.uniform_model_nonzero` gives strictly positive root budgets
under the uniform schedule law, so the financial architecture has a checked
nonzero-volatility example.


`ScheduleBounds.uniform_moment_bound` proves a common pointwise bound for
all schedule probabilities and all labeled states. With
`Γ = 1 + ∑events (|log S| + S) + ∑future pairs B`, the exact bound is
`Γ² < (1 + 8*(6*log 2 + 729/64) + 28*c)² + 1`.
`ScheduleMoments` proves stock forwards equal one, expected window log variance
`3*c/2`, VIX second moments `c/2`, and the overlap log cost
`c*(j-i)/6` whenever every activity bit has mean one half. These assumptions
are discharged from the standing SPX prefix marginals in the integration.

Focused direct-compiler checks of `ScheduleBounds` and `ScheduleMoments`
finished with exit status zero. The largest of those checks reported
368,754,432 bytes peak macOS memory footprint and 2,182,332,416 bytes maximum
resident set size. The two operating-system metrics differ; neither is the
Lean internal allocation cap. Earlier 138 MB readings taken around
`lake env lean` measured the wrapper and were not valid Lean-footprint figures.
The definitive integrated build and headline axiom output belong in the
project-level `VERIFICATION.md`.

## Same-panel hidden-information extension

The default verification now also imports `ExtensionHeadline`. Its full
financial theorem constructs the same vanilla panel for every `0≤ε≤1` with
hidden activity and fixing-time signals, retaining the original root budgets
and common moment bound. `BroadContract` declares the broader class without
an assumed existence field. `HiddenCertificate` checks exact integer data;
`FiniteConditioning`, `HiddenModel`, and `HiddenQuotes` turn it into a complete
calibrated finite financial law. `Mixture` proves branch revelation at event 1
preserves all structural equations, ordinary quotes and window log identities.
The entire family uses one 6592-state carrier.

The one-command verifier also checks that the hidden-witness JSON matches the
literal Lean data. This check needs only Python's standard library; SciPy is
needed only to rerun numerical discovery. No continuous realization is
imported or claimed. See `../EXTENSION.md` for the frozen broader contract and
the difference from the published early-revealed architecture.
