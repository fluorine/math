# Independent extension statement audit

Date: 2026-10-15. An Astra explorer received the informal extension and formal
headline and performed a read-only adversarial review. It did not run Lean or
repeat the literature search. Kernel verification is recorded separately.

No material mathematical or statement defect was found in the inspected
definitions and proof sources. The review checked:

- `Broad.FitsPanel` uses the original ordinary SPX/VIX price functions,
  uniform SPX baseline, and `QuoteContract.targetCall`. No budget or signal
  becomes an observed quote.
- The headline returns an actual `FiniteModel`, the original initial data
  and moment bound, all calls, stock forwards, and full-history window-log
  identities. Conditional structural rows are proved by the constructors.
- Finite conditional averaging separately treats zero mass. Signal
  identification invokes proved positive latent history masses. Mixture
  equations multiply by branch weights and remain valid at both endpoints.
- The mixture root is trivial. The branch is revealed at event 1, and common
  root budgets make the root tower/adaptation equations valid. Hidden
  histories retain all completed activity/sign observations and all signals
  revealed so far.
- `Broad.momentSize` uses actual model coordinates and the same bound. Both
  constructed branches retain the original stronger pointwise stock and
  cell-budget bounds. Exact positive probability tables rule out vacuity.
- The finite certificate uses ordinary kernel computation and exact
  real-valued algebra; the conditional model and ordinary-call bridge are
  separate proved steps.

The reviewer identified one wording risk: the witness uses additional fixing
signals and a mixture branch on a 6592-state carrier. It is not shown to be
merely a coarsening of the original filtration on the old 4096 states. The
broader contract permits these states and signals explicitly. EXTENSION.md
now states this distinction directly, and the result should be described as
compatibility when hidden activity and fixing-time signals are allowed.

A finite witness suffices to refute incompatibility in any broader
finite-event class containing it. It establishes neither continuous-path
realization, general pairwise completeness, nor compatibility under an added
restriction forbidding supplementary signals. Qualitative information
sensitivity is prior art; the novelty audit makes only a provisional claim
for this exact panel's constructive resolution.

The primary researcher also inspected the conditional-average tower proof,
hidden-model constructor, mixture root and positive-date rows, and ordinary
quote bridge. Agent agreement is not evidence of mathematical truth: the
complete fresh Lean build and its transitive axiom audit are required.

The required complete fresh build subsequently passed on 2026-10-15: 27
modules, exit status 0, and 39 distinct audited declarations using only the
three accepted foundational axioms. The full output is preserved in
`extension-verification.log`. This build evidence is separate from the
reviewer's read-only assessment.
