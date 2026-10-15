# Result — 15 October 2026

**The compact-generator target is met by a proved construction.** A separate
coupled-profile theorem also gives a strictly smaller ordinary-sensitivity
bound on the same explicit seed. The results have independent AI-agent mathematical
and code review, with bounded executable checks. Historical novelty remains
provisional; these are not claims of peer review or Lean formalization.

For public reading, start with the [typeset note](output/pdf/sensitivity-note.pdf),
the [repository overview](README.md), and the
[completed novelty audit](publication/NOVELTY_AUDIT.md). The latter gives
source-by-source comparisons and an explicit scalar countermodel showing
that the new inequalities do not follow from the old numerical system.

## Uniform deterministic labels

For every integer q>=3, set

    M = [13(q−1)]²,  r = 13(q−1),  k = 2M²+1.

Orient i→j when 1<=(j−i) mod k<=M². Encode each vertex in 13 base-q digits.
At the first differing position, label the edge by that position and the
source digit's rank among digits other than the head digit. This uses r
labels. Every head-coherent set has at most 15 vertices, for **any** tournament
orientation; hence the cyclic regular tournament satisfies exactly the
family-132 forbidden-16 contract.

One orientation/label query uses O(log M) bits of storage and
O((log M)²) bit operations. There is no edge table, random seed, witness
advice, or exhaustive witness search. At q=3, M=676 and k=913953; the
construction is proved for the entire infinite family, not just that case.

The complete proof is [CONSTRUCTOR.md](proofs/CONSTRUCTOR.md), with executable
interface `SuccinctTournament(q)` in [label_contract.py](checks/label_contract.py).
[MANUSCRIPT.md](MANUSCRIPT.md) includes the full label proof and the explicit
labels-to-Boolean-functions corollary, dimensions, description length,
evaluation cost, zero witnesses, OR balancing, and amplification.

## Stronger ordinary/joint profile theorem

[PROFILE.md](proofs/PROFILE.md) proves new piecewise bounds by showing that
most target repairs necessarily cross two distinct child thresholds and by
coupling the target/gate candidate counts. This improves the actual
four-profile estimate; it is not just a numerical sweep or the immediate
replacement of the source's coefficient 16 by 15.

The fixed explicit comparison uses q=1001, recursion depth d=17,
M=169000000, r=13000, k=57122000000000001, and c=164900179 OR copies.
Both analyses concern exactly this same seed and the same zero-block
witness family. Its dimension is the 373-digit integer

    n = c · 19 · M · (k r)^17,

and its block lower bound is B=c M k^17. Iterating the source proof with
its immediate refinements gives a sensitivity bound A_old; the new theorem
gives A_new<A_old. The exact integers and checks are in
[seed-certificate.json](checks/seed-certificate.json).

| Bound on this same seed | Certified exponent, rounded for display |
|---|---:|
| Existing argument plus immediate refinements | 2.01541090309158218… |
| New coupled-profile theorem | 2.01541154731147847… |

These are rigorous exponents from alpha=log(B)/log(A), not the unknown
exact sensitivity of the seed. The strict comparison follows already
from A_new<A_old with unchanged B,n, and is corroborated by disjoint
70-digit intervals. Exact integer powers also establish alpha>2.0154.
Repeated disjoint composition gives functions on n^m bits with
bs(F_m,0)>=s(F_m)^alpha and unbounded block sensitivity.

The numerical gain is small. An exponent above 2.0154 already follows from
the existing recurrences with better parameters; it is **baseline**, not
the novelty claim. Neither the optional finite scan nor this seed is
claimed globally optimal. See [BASELINE.md](proofs/BASELINE.md).

Both calculations use the no-coherent-16 contract. For the chosen seed,
seven leading base-1001 digits are common, so the label theorem actually
gives a coherent-set bound of eight. This additional direct corollary is
unused in both calculations; the reported comparison isolates the profile
refinement at a fixed contract, rather than optimizing this particular seed.

## Reproduce

From the isolated worktree root:

```sh
python3 topics/sensitivity-separation/scripts/reproduce.py --fetch-sources
```

Python 3.9+ standard library only. The source option downloads or hash-checks
63 pinned files; omit it for a fully offline check. All computation is
serial with per-process timeouts. The command checks 129088 small labelled
tournaments, 46656 local profile configurations, exact counterexample
templates, and the saved fixed-seed certificate. The written induction and
profile proofs establish the infinite statements; finite tests do not.
No large tournament or Boolean truth table is materialized.

See [VERIFICATION.md](proofs/VERIFICATION.md) and
[reproduction.log](checks/reproduction.log) for audit scope and run output.
No Lean build was run, and no remote branch was pushed or merged.

## Novelty and continuation

First-difference coloring, Cole–Vishkin position-plus-source-symbol methods,
gated tournaments, OR balancing, and composition are established ideas.
The precise claims here are the arbitrary-orientation head-coherence bound,
its exact succinct family-132 instantiation, and the stronger coupled-profile
inequality. The 15 October literature refresh found no matching theorem,
but cannot guarantee priority. [NOVELTY.md](NOVELTY.md) and
[LITERATURE.md](sources/LITERATURE.md) record this boundary and antecedents.

The requested mathematical construction no longer has a missing implication.
Further work could establish a formal Lean proof or investigate better
profile/seed parameters; neither is represented as completed or necessary
to the written theorem. Broader historical comparison remains the main
uncertainty about novelty.
