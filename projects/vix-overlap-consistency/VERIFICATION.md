# Verification record

**PASS — 2026-10-15, exit status 0.** The complete scoped financial theorem and its local dependency closure were freshly compiled. This verifies the declared finite architecture, not unrestricted SPX/VIX markets or mathematical novelty.

## Reproduce

From `projects/vix-overlap-consistency` in the research checkout:

```sh
scripts/verify.sh
```

The recorded run used:

```sh
scripts/verify.sh > notes/verification.log 2>&1
```

It ended with:

```text
PASS: 19 local modules freshly compiled; exit status 0.
```

The entry point first checks that `certificates/exact.json` matches the literal Lean data. It then verifies exact compiler/dependency revisions and unchanged dependency sources, rejects local proof placeholders, custom axioms and native computation oracles, rebuilds every local module in the import closure, and checks every printed axiom list. All 22 audited declarations passed. Linter warnings about unused simplifier arguments or deprecated names are present; there are no build errors.

The build reuses pinned upstream Mathlib artifacts but never reuses a local proof module without recompilation. It is a clean local-source verification, not a from-source rebuild of the whole Lean/Mathlib ecosystem. Missing dependencies are restored from the checked-in manifest; the no-dependency bootstrap path was inspected but not separately run from an empty download cache.

## Pinned versions

| Component | Pin |
|---|---|
| Lean | 4.34.1, arm64-apple-darwin24.6.0 |
| Lean compiler commit | `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (v4.34.1) |
| Transitive packages | Exact revisions in `formal/lake-manifest.json` |

`formal/lean-toolchain` pins the compiler. Set `VIX_LEAN=/absolute/path/to/lean` if it is not on PATH. On this Mac, the script also recognizes `/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin/lean`. Initial dependency retrieval requires network access. No BrownianMotion or formal-mathfin declaration is imported.

## Headline and axioms

The full statement is `VixOverlap.financial_three_window_obstruction` in `formal/VixOverlap/Headline.lean`. It includes proper-panel structural witnesses, full-panel impossibility, fixed root budgets, positive witness weights for ε>0, a common moment bound, full window conditional-log identities, actual-SPX-log T2/T4 tests, and the exact positive separation margin. `Audit.lean` prints the relevant definitions/statements and requests transitive axiom dependencies.

The recorded output includes:

```text
'VixOverlap.financial_three_window_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.QuoteContract.vanilla_three_window_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.ScheduleModel.model' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.quoted_second_moment_log_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.quoted_overlap_log_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.exact_separation_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every other audited declaration has the same three foundational axioms. The complete output is in `notes/verification.log`. There is no `sorry`, `admit`, `sorryAx`, substantive custom axiom, native computation oracle, or external solver assumption in the main proof closure. Ordinary `decide` proves finite integer facts; proved finite-sum identities lift the certificate to arbitrary real probabilities. Logarithms and square roots are exact real expressions.

## Statement and library audit

An independent explorer compared the informal theorem with the formal declaration and definitions. Initial findings required the full structural constructor, window log relation, ordinary-quote identification, common budgets/bounds, actual-SPX-log tests, and an integrated axiom audit. These were implemented. The final source audit found no material statement-level gap; its findings and limits are in `notes/statement-review.md`.

T1 is established by actual probability laws, stock positivity, `model_stock_forward`, and the common pointwise moment bound. T2 and T4 appear explicitly in the headline. T3 is stronger than testing a finite selection of inequalities: every proper subpanel has an actual filtered law. `uniform_model_nonzero` provides a nonzero-variance admissible example. Additivity is proved in `BudgetAlgebra.lean`. Conditional equations remain unnormalized on zero-mass histories.

The relevant Mathlib declarations for real logarithms, square roots and prime factorization were inspected. Strict stock positivity keeps the diagonal identity in the intended logarithm domain; square-root squaring uses a proved nonnegative argument. Imported results do not assume the desired realization or obstruction. The exact dependency map is in PROOF_MAP.md.

## Resource and discovery record

Builds were serial, single-threaded, and `nice 19`, with Lean's internal allocation cap set to 4,096 MB. Direct measurement of the final expectation module gave a peak macOS physical footprint of about 352 MiB; mapped maximum RSS was about 2.18 GB. Earlier Lake-wrapper footprint measurements were discarded because the wrapper spawns a Lean child. No other task's active process was modified.

The numerical script discovers candidates only. `scripts/exactify.py` reconstructs rational data and checks it with Python fractions; its successful gap 1/32 check is supporting evidence, not the theorem. The final Lean certificate checks the data and its mathematical implications independently of the numerical LP. Failed model-design approaches are recorded in THEOREM.md and `notes/model-audit.md`.

## GitHub publication verification

The full local command was rerun successfully before the authorized publication on 2026-10-15, again compiling 19 modules and passing all 22 axiom audits. The recorded log above is from that rerun. `.github/workflows/vix-overlap-consistency.yml` runs the same complete verifier on pushes and pull requests that affect this project.

CI installs the exact Lean 4.34.1 Linux release archive and checks its official SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`. Checkout is pinned to `3d3c42e5aac5ba805825da76410c181273ba90b1`. Dependencies and Mathlib artifacts are freshly retrieved over the network when absent. The Ubuntu 24.04 runner image is maintained rather than bit-pinned; compiler and dependency identities are independently checked by the verifier. Remote run outcomes are recorded by GitHub Actions and must not be inferred from this local pass.
