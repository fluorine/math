# Explicit labels and refined profiles for a sensitivity construction

**[Read the mathematical note (PDF)](output/pdf/sensitivity-note.pdf)**
· [LaTeX source](publication/sensitivity-note.tex)
· [Detailed novelty audit](publication/NOVELTY_AUDIT.md)
· [Follow-up review and sharper comparison](publication/FOLLOWUP_REVIEW.md)
· [Independent-review prompt](publication/EXTERNAL_REVIEW_PROMPT.txt)

This note makes the tournament labels in the OpenAI family-132 construction
uniformly computable on an infinite parameter family, and strengthens the
local counting argument used to bound ordinary sensitivity. It was developed
with AI assistance and is shared for mathematical review.

Sensitivity counts individual bits whose flips change a Boolean function.
Block sensitivity counts disjoint nonempty groups of bits whose separate
flips change it. The starting point is the existing
[family-132 superquadratic separation](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026).

## What the note proves

**Explicit labels.** Encode vertices as words of length $h$. Label an arc by
its first differing coordinate and its source digit, with the digit encoded
injectively relative to the head. In every tournament orientation, a set
whose incoming labels agree at each head has at most $h+2$ vertices. An
elementary bucket induction proves this bound.

For each integer $q\ge3$, take

$$M=[13(q-1)]^2,\qquad r=13(q-1),\qquad k=2M^2+1.$$

The cyclic regular tournament on $k$ vertices, represented by 13 base-$q$
digits, then has $r$ labels and no head-coherent 16-set. Each edge query
takes $O((\log M)^2)$ bit operations and $O(\log M)$ space. No stored edge
table, witness advice, or random seed is required.

The [follow-up proof](publication/FOLLOWUP_REVIEW.md) uses the chosen cyclic
orientation to sharpen the cap to $H+1$, where $H=\lceil\log_q k\rceil$.
The uniform bound is fourteen, attained at $q=3$; the exact maximum for the
fixed $q=1001$ seed is seven. These are direct consequences of the bucket
argument and transitive final-digit buckets.

**Refined profiles.** Most candidate target repairs must cross two nested
child thresholds simultaneously. At most one target is an exception, and
the target and gate counts constrain one another. This gives six branches
for the ordinary zero profile and five for the joint zero profile; the
one-side bounds remain those of the source. The complete proof, including
the exceptional head reassignment and the joint-index argument, is in the
note and [PROFILE.md](proofs/PROFILE.md).

## Precisely what is new, and what is inherited

| Part | Status |
|---|---|
| First-difference coordinate plus source digit | Classical local-asymmetry method; see [Cole–Vishkin](https://doi.org/10.1016/S0019-9958(86)80023-7). |
| Excluding the head digit from the palette; parameter substitution and query cost | Elementary encoding and arithmetic consequences. |
| Arbitrary-tournament head-coherent bound $h+2$ | Specific directed adaptation proved here; no matching theorem was located in the audit. Historical priority remains provisional. |
| Replacement of the family-132 random labels | Application of that bound to the exact source contract. |
| Cyclic-family cap $H+1$, uniform fourteen, and exact seven at the fixed seed | Elementary corollaries of the label argument; proved in the follow-up addendum. |
| Nested predicates, four ordinary/joint profiles, zero-block witnesses | Inherited from family 132. |
| Target coefficient 16 reduced to 15, tighter gate envelope, base bound $d+1$ | Immediate consequences of the existing proof; included in our baseline. |
| Joint accounting of target repairs, coupled target/gate counts, six/five profile branches | Additional combinatorial arguments relative to the inspected source. |
| OR balancing, composition, and exponent $\log B/\log A$ | Established arguments; OR identities already appear in [Ambainis–Sun, §4, Lemma 1](https://arxiv.org/html/1108.3494v1). |

The [audit](publication/NOVELTY_AUDIT.md) gives the exact reductions, source
locators, alternative terminology searched, and limitations. Absence from a
literature search does not establish priority. The contribution is a modest
explicit-construction and proof refinement; the note does not claim a new
separation architecture or a record exponent.

## A comparison on the same seed

Fix $q=1001$, recursion depth $d=17$, $M=169000000$, $r=13000$,
$k=57122000000000001$, and $c=164900179$ OR copies. Both analyses use
exactly the same function, zero-block witnesses, and dimension

$$n=c\cdot19\cdot M(kr)^{17},\qquad B=cMk^{17}.$$

The dimension is a 373-digit integer. Writing $A$ for the sensitivity upper
bound, the exponent certificate is $\alpha=\log(B)/\log(A)$.

| Analysis using the exact coherence cap seven | Certified exponent, abbreviated |
|---|---:|
| Existing proof with its immediate refinements | 2.0154112468376777104… |
| Coupled-profile theorem | 2.0154115475113140209… |

The strict improvement follows from the exact inequality $A_{\rm new}<A_{\rm old}$,
with $B$ and $n$ unchanged. The
[follow-up certificate](checks/independent-audit.json) records exact integers
and disjoint rigorous logarithm intervals. An exponent greater than
2.0154 already follows from the existing proof; it is not the novelty claim.
These are bounds, not exact sensitivities, and the seed is not claimed optimal.

The original PDF and [original certificate](checks/seed-certificate.json)
compare cap-fifteen bounds, giving 2.0154109030915821803… versus
2.0154115473114784763…. That comparison remains valid under its stated
contract. The table above applies the additional easy information to both
analyses, with the same OR-copy count. The gain remains positive, approximately
$3.0067\times10^{-7}$. Even the sharper immediate baseline stays below the
original cap-fifteen coupled result. The
[addendum](publication/FOLLOWUP_REVIEW.md) supplies the proof and all three
cap-fifteen/eight/seven comparisons. No optimality claim is made.

## Reproduce

From the repository root, with Python 3.9 or newer:

```sh
python3 topics/sensitivity-separation/scripts/reproduce.py --fetch-sources
```

Only the Python standard library is used. The optional `--fetch-sources`
downloads or hash-checks 63 pinned source files. Omit it for offline checks.
The command runs serially with timeouts and verifies 129088 small labeled
tournaments, 46656 local profile configurations, exact obstruction templates,
and the fixed-seed arithmetic certificate. It does not instantiate the large
tournament or the Boolean truth table.

Run the separately implemented follow-up audit with:

```sh
python3 topics/sensitivity-separation/checks/independent_audit.py
```

It derives the same-seed comparisons from the manuscript equations, checks
the seven-vertex witness, and independently encloses logarithms using rational
series bounds and outward integer rounding. It also rechecks the original
exact-power certificates. The standard reproduction above was rerun from a
clean checkout with an empty source cache; all checks passed.

The infinite claims rest on the written proofs. Finite checks, source scans,
and independent AI-agent review are supplementary evidence. The new theorems
have not been formalized in Lean or reviewed by a human referee. See the
[verification report](proofs/VERIFICATION.md) and
[recorded run](checks/reproduction.log).

The PDF is built from one standalone LaTeX file. With Tectonic installed:

```sh
tectonic --outdir topics/sensitivity-separation/output/pdf topics/sensitivity-separation/publication/sensitivity-note.tex
```

## Further reading

- [Full source comparison and novelty audit](publication/NOVELTY_AUDIT.md)
- [Generator proof and mixed-radix variants](proofs/CONSTRUCTOR.md)
- [Coupled-profile proof and exact obstructions](proofs/PROFILE.md)
- [Existing-formula baseline](proofs/BASELINE.md)
- [Source inventory and hashes](sources/manifest.json)
- [Earlier working manuscript](MANUSCRIPT.md)

Corrections, counterexamples, and references to an existing version of either
specific lemma are welcome. The novelty audit is dated 15 October 2026.
