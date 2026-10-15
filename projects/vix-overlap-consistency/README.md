# Three-window vanilla inconsistency in a finite activity-schedule market

The project constructs an exact family of ordinary SPX/VIX call panels in a
fixed finite structural class. Every one- and two-window subpanel has a full
filtered martingale law. The three-window panel has none in that same class.
The class is defined before the numerical search; all real probability weights
on all 64 activity schedules are allowed. It is not a solver discretization of
an unrestricted market.

The windows are [2,5], [3,6], and [4,7], with common tenor three in the declared
time unit. The separation margin is `(1−30ε)/32` for every real
`0≤ε<1/30`. Proper-panel witnesses put positive mass on every one of the 4,096
raw states when `ε>0`.

Read [THEOREM.md](THEOREM.md) for the exact contract,
[MANUSCRIPT.md](MANUSCRIPT.md) for the mathematical argument,
[NOVELTY.md](NOVELTY.md) for the qualified literature assessment, and
[VERIFICATION.md](VERIFICATION.md) for the current build evidence.
[PROOF_MAP.md](PROOF_MAP.md) maps the argument to Lean declarations.

From this project directory:

```sh
scripts/verify.sh
```

The script checks the pinned Lean/Mathlib revisions, freshly compiles the local
proof closure serially, and audits the headline axiom output. Numerical discovery
and exact Python reconstruction are separate from this proof entry point.

This is a model-consistency result within the stated architecture. It does not
claim executable arbitrage, arbitrary-state impossibility, continuous
realization, or global minimality. The broader research question remains open.
