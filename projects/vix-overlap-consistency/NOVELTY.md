# Provisional novelty audit

Audit date: 2026-10-15. **No matching public resolution found as of 2026-10-15** in targeted searches. This does not establish novelty. Formal proof status is recorded separately in VERIFICATION.md.

* [Huang, Kspectra working paper](https://kspectra.ai/papers/common-budget-certification-spx-vix/): displayed September 2026, accessed 2026-10-15, no explicit revision identifier. Lemma 2.1 supplies the full-history finite budget model. Proposition 3.5 is a two-window necessary overlap inequality. Example 4.2 uses two overlapping vanilla windows. Example 4.1 uses abutting windows and extra joint claims. Neither is a triple vanilla panel with all pairs feasible. The general common-budget framework, compact separation, and claimed continuous realization are prior art, not this project's proposed contribution.
* [Acharya et al., arXiv:2609.04087v1](https://arxiv.org/html/2609.04087v1): submitted 2026-09-03; version history inspected 2026-10-15 lists only v1. Theorem 3.2 concerns tiled windows with common seam marginals. Its block-preserving Markovization cannot be applied directly to overlapping intervals. Theorem 3.4 concerns non-identification of inter-block dependence. Section 6 leaves the overlapping reference construction outside Proposition 6.1.
* [SSRN 7399598](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7399598): canonical and alternate abstract URLs failed. The author page links to it, but SSRN metadata/latest version has not been independently verified. Do not assert all versions were read.

Searches included exact source titles and combinations of SPX, VIX, three-window, overlapping windows, higher-order consistency, pairwise feasibility, sum-functional, and activity schedule, plus indexed GitHub and X results. X access was search-index coverage only, not an authenticated exhaustive search. No proof matching the proposed target surfaced. Social posts are not used as mathematical evidence.

Precise proposed contribution: an explicit family resolving pairwise-versus-triple feasibility of ordinary overlapping-window VIX strips with a fixed SPX strip in the activity-schedule market of THEOREM.md, with complete filtered-law witnesses, an exact positive margin, and a machine-checked ordinary-quote bridge. Merely finding a marginal compatibility polytope facet is supporting machinery. The finite financial embedding is the contribution being assessed; it does not establish an unrestricted continuous-market obstruction.

## Audit after finding the candidate

The candidate has prefix-binomial marginals and three sliding-sum marginals, with robust mixture gap (1−30ε)/32. Searches for binary sliding sums, prescribed partial-sum distributions, binomial random-walk marginals, overlapping sum distributions, discrete tomography, marginal-polytope cycles, and VIX pairwise consistency found no exact matching construction.

A final same-day refresh searched `"VIX" "three" "pairwise" "overlapping" consistency`, `"SPX" "activity schedule" VIX`, and `"binomial" "sliding sums" "marginals"`. It returned the already-audited Kspectra examples and unrelated results, not a matching public resolution. The arXiv abstract/version page remained accessible; the SSRN canonical URL again returned an internal access error. Search silence and inaccessible SSRN revisions remain limitations.

General pairwise-versus-global incompatibility is classical: [Wainwright–Jordan, Example 4.1 and equation (4.10)](https://people.eecs.berkeley.edu/~jordan/sail/readings/wainwright-jordan-fnt.pdf) discuss binary cycles; [Sontag–Jaakkola, NeurIPS 2007, Theorem 2](https://proceedings.neurips.cc/paper/2007/file/2b323d6eb28422cef49b266557dd31ad-Paper.pdf) study projected cycle inequalities. We have not established that this particular inequality is equivalent or inequivalent to a triangle inequality. Do not claim a new general theory of marginal compatibility.

Because the full schedule is revealed before returns, the candidate obstruction is a finite marginal problem. It does not establish a new information-revelation or tower obstruction. The potentially new content is the explicit ordinary-SPX/VIX embedding, same-class proper-subpanel laws, and particular exact family. This is worth proving as a scoped counterexample but is insufficient grounds to advertise a major unrestricted mathematical-finance theorem. The unrestricted problem remains unresolved.

## Same-panel extension audit, 2026-10-15

The local extension constructs a compatible hidden-information law for the
same panel. Its precise contribution is resolving this panel's fate after
removing early revelation, with an exact 39-state latent witness and a checked
filtered mixture for the parameter family. This is a relevant disproof of a
stronger interpretation of our example. It is not a general completeness
theorem for pairwise tests.

The qualitative information mechanism is already explicit in
[Huang, Section 2.3](https://kspectra.ai/papers/common-budget-certification-spx-vix/):
Proposition 2.11 characterizes the effect of revealing a mark, Example 2.12
preserves stock martingality while changing the VIX budget, and Definition
2.13 distinguishes preservation of conditional values from unconditional
calibration. Those ideas are prior art. We do not claim to discover that VIX
depends on the filtration. The new table addresses the specific three
overlapping windows and unchanged all-strike panel defined here.

The same-day extension refresh searched `"VIX" "hidden" "overlapping"
"consistency" 2026`, the exact common-budget paper title, and the arXiv
identifier. The author HTML was reread; it still displays September 2026
without a revision identifier. The arXiv version page still lists only v1.
Indexed SSRN metadata now reports “last revised 4 Sep 2026,” but the direct
delivery URL returned an access error and the PDF was not independently read.
This improves the metadata record without removing the source-access limit.
No matching public resolution of this explicit panel was found as of
2026-10-15. Novelty remains provisional; formal correctness and novelty are
separate assessments.
