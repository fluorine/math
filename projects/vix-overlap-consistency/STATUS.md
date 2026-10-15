# Research status

2026-10-15: the scoped finite-architecture theorem is complete and kernel checked. The broader unrestricted-market problem remains unresolved, and mathematical novelty remains provisional.

## Verified result

For every real 0≤ε<1/30, the explicit three-window vanilla panel in THEOREM.md has a compatible filtered law for every proper subpanel and none for all three windows in the same early-revealed activity class. The standing SPX panel is fixed. The proof quantifies over every real probability law on all 64 schedules; it does not restrict candidate weights to a numerical grid.

The complete theorem includes the positive margin (1−30ε)/32, the frozen second-moment and pairwise overlap tests with actual SPX log expectations, common root budgets, common moment bounds, and full-history window log identities. The model construction proves positivity, adaptation, every martingale row, every diagonal log row, and every tower row. All 4,096 raw states are available under every subpanel; the supplied witnesses give each positive mass when ε>0.

`scripts/verify.sh` completed with exit status 0 on 2026-10-15: 19 local modules freshly compiled and all 22 declared axiom audits passed. Each reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The full output is `notes/verification.log`. No unresolved Lean lemma remains in the scoped theorem. The independent statement audit found no material gap after the recorded repairs.

## Scope and novelty

The class has an economically explicit but restrictive mechanism: the entire active/frozen variance schedule is revealed at event 1, and independent fair signs subsequently produce stock returns. The new candidate contribution is the exact ordinary-SPX/VIX embedding and family, not the general marginal-polytope phenomenon or the existing budget framework. No matching public resolution was found in the documented searches as of 2026-10-15. Latest SSRN access failed, so novelty is not certified.

No unrestricted continuous-state impossibility, continuous realization, executable arbitrage, sharp separator bound, general return-amplitude theorem, or global minimality is claimed. The broader research objective remains incomplete to that extent. A future extension must address arbitrary admissible transitions and information states; merely locking SPX/VIX supports would not discretize latent budgets.

## Repository and reproducibility

The inspected checkout is `/Volumes/2tb/math`, remote `https://github.com/shjvandekamp/math.git`. Work is isolated in `/Volumes/2tb/math/.worktrees/vix-overlap-consistency`, branch `research/vix-overlap-consistency`, from commit `07078df`. The primary checkout's unrelated `.DS_Store` and other research worktrees were preserved. Nothing has been pushed or published.

Project files include the theorem/model contract, manuscript, novelty audit, proof map, complete Lean sources, pinned manifest, numerical discovery script, exact JSON certificate, generator, verification entry point, build output, and independent review findings. The exact finite certificate is checked by Lean; Python discovery/reconstruction is not a proof oracle.

Next executable step for reproduction, from this project directory: `scripts/verify.sh`. A larger-class research attempt should first define and justify a sound relaxation of its latent budgets and information, then test this panel; no such extension is presently proved. No background computation or continuing research is promised after this session ends.
