# Novelty and target audit — 15 October 2026

The completed, deeper comparison is in
[publication/NOVELTY_AUDIT.md](publication/NOVELTY_AUDIT.md). It distinguishes
the classical first-difference mechanism, the specific directed adaptation,
immediate source-proof corollaries, and the additional profile arguments.
This file preserves the original target and research-stage audit.

Initial status: research targets, not established results. The target/audit
sections below were written before mathematical experiments. The final
outcome section records the subsequent proved results and their scope.

## Exact primary target

For an explicitly stated infinite set of integers M >= 3, put k = 2 M² + 1 and
r = ceil(sqrt(M)). Construct a regular tournament on {0,...,k-1}, of outdegree
M², and labels a(i,j) in {0,...,r-1} on directed edges. For every 16-element
set I and every assignment m:I -> {0,...,r-1}, at least one directed edge
i -> j inside I must satisfy a(i,j) != m(j). Labels belong to the **head** j;
vertices with no incoming edge in I impose no constraint on their m(j).
This is exactly Lemma 2.1 of the pinned family-132 manuscript, with zero-based
indices substituted consistently. A condition excluding only transitive
sets, monochromatic edge sets, or source-coherent sets is insufficient.

Required explicitness: a uniform deterministic algorithm with a compact
parameter description and no witness advice/nonuniform table, evaluating
orientation and a single label in polynomial time in log(M) and the index
bit lengths. Prove the contract for the entire stated infinite parameter
family. Random existence, unrestricted first-witness exhaustive search, and
small examples do not satisfy this target. Weaker explicitness is to be
reported separately and checked against prior work.

## Secondary target

Prove a new structural inequality for the actual nested predicates or their
ordinary/joint sensitivity profiles, with strict improvement over the full
published four-profile system. Propagate the inequality through balancing
and composition with certified alpha = log(B)/log(A), dimension, description
length, and construction cost. Merely solving or optimizing the existing
recurrences, tightening their displayed coarse scalar relaxation, or choosing
better parameters is baseline analysis, not the target contribution.

The published recurrence, ordered as S0,S1,J0,J1, is

    S0_next <= 16*S0 + S1 + 3*J1
    S1_next <= M²*S0 + r*S1
    J0_next <= 16*S0 + 3*J1
    J1_next <= M²*J0 + r*S1.

Initially S0 <= d+2, S1 <= (d+2)M, and J0=J1=0. Predicate count is
H_l=d+1-l; at l=d the joint maxima are zero by definition. Exact definitions
and the implication chain are independently reconstructed in proofs/VERIFICATION.md.

## Existing ordinary-sensitivity baseline

Pinned OpenAI math revision 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
preprint dated 25 September 2026, proves for every d>=1 and M>=9^(d+1)
a seed of dimension n=(d+2) M² ((2 M²+1)ceil(sqrt(M)))^d, with f(0)=0,
s(f)<=A=2(d+2)M^(d+1), and bs(f,0)>=B=M²(2M²+1)^d. Thus
bs(f)/s(f)² >= 2^d/[4(d+2)²], unbounded in d. Its d=9 seed gives
alpha=log(B)/log(A)>2 under repeated composition. The four recurrences hold
already for M>=3; the condition M>=9^(d+1) belongs to its coarse quantitative
lemma. Exact recurrence iteration and better permitted parameter choices must
therefore be counted as existing-formula baseline.

Earlier ordinary-s results cited there include Rubinstein's quadratic
separation, Virza's (s²+s)/2, and Ambainis–Sun's (2s²-s)/3. The current
search found no stronger ordinary-s theorem than family 132; this is a
limited literature finding and does not establish guaranteed priority.

## Meiburg relationship

Alexander Meiburg, arXiv:2608.00851v1, submitted 1 August 2026, uses related
gated tournaments and discusses a deterministic cyclotomic heuristic.
Its proved headline comparison is bs versus spectral sensitivity lambda,
not ordinary sensitivity s. Since lambda <= s, bs >= lambda^alpha does not
imply bs >= s^alpha. Family 132 changes the forbidden-label condition and
tracks simultaneous threshold crossings to control ordinary sensitivity.
No claim here treats the gated-tournament architecture itself as new.

Timeroot/BS_Lam head inspected in the refresh:
7bd39a8d41ee7910d3296d0477ad18f8fff9d870 (28 August 2026).
Its build/status claims are source evidence, not locally rerun verification.

## Public search refresh

Searches on 15 October 2026 included exact paper ID, Timeroot/BS_Lam,
OpenAI family 132, and combinations of ordinary sensitivity, block
sensitivity, generator, explicit construction, superquadratic, tournament,
gate, and profile. The independent verifier found no matching proved
efficient exact-contract generator or stronger coupled ordinary-s theorem.
Search coverage and individual URLs/queries are recorded in
sources/LITERATURE.md. An adjacent elementary-symmetric-Boolean-functions
paper is a different function class. Absence in these searches is not proof
of novelty. Source version, theorem scope, and any new candidate's actual
substantive difference require a final recheck.

Primary sources:

- https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026
- https://arxiv.org/abs/2608.00851
- https://github.com/Timeroot/BS_Lam/tree/7bd39a8d41ee7910d3296d0477ad18f8fff9d870

## Outcome after construction and independent audit

The exact label target is now met on the infinite family
M=[13(q−1)]², q>=3, by the first-difference rule proved in
proofs/CONSTRUCTOR.md. A head-coherent subset of h-digit words has size
at most h+2 under any tournament orientation. With h=13, the palette
has r=13(q−1) labels and contains exactly the permitted head assignments;
the cyclic orientation supplies regularity. Per-edge bit time is
O((log M)²), storage O(log M), with no preprocessing or witness advice.

The substantive secondary result is the new six/five-branch coupled-profile
inequality in proofs/PROFILE.md. Most target repairs cross a weaker child
predicate and the strongest child predicate together, so they can be charged
to J0 rather than S0. The source/gate interaction also limits their joint
counts. The independently checked fixed certificate propagates this through
OR and composition, obtaining a strictly smaller A and larger log(B)/log(A)
at identical B and seed dimension. It is not merely an optimization of the
published inequalities. The attained exponent above 2.0154 alone is not
novel: the source baseline already supplies that numerical threshold.

The refined literature comparison identified classical first-difference
colorings and Cole–Vishkin position-plus-source-bit labels as antecedents.
The candidate novelty is limited to the precise directed coherence theorem,
its exact family-132 application, and the proved profile refinement. No
matching prior theorem was found in the scoped searches, but priority is
not guaranteed. All mathematical claims are written proofs with independent
review and finite implementation/arithmetic checks, not Lean formalizations.
