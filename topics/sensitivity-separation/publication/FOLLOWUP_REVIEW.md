# Follow-up review and a sharper fixed-seed comparison

15 October 2026. Reviewed publication: commit
[`00820a69fbaeab0f20d4b099153d3bf8c6b27be9`](https://github.com/shjvandekamp/math/tree/00820a69fbaeab0f20d4b099153d3bf8c6b27be9).
This addendum records a fresh proof and arithmetic review, an elementary
strengthening of the label bound, and its numerical consequences.
The current [manuscript](sensitivity-note.tex) and
[PDF](../output/pdf/sensitivity-note.pdf) now incorporate the cyclic bound,
the generic-cap profile theorem, and the matched cap-seven comparison below.
This report retains the findings and numerical context of the earlier review.

**No gap was found in the reviewed label or coupled-profile proofs, and the
cap-fifteen numerical certificate reproduced.** The actual cyclic construction
has a better coherence bound than that calculation used: at most fourteen
throughout the parameter family, and exactly seven for the fixed seed.
Applying seven to both analyses still gives a strict coupled-profile gain.
These additional bounds are elementary consequences of the existing argument,
not separate claims of a new method or historical priority.

The primary reviewer participated in the original work. Three fresh-context
AI agents separately reviewed the label/literature argument, the profile proof,
and arithmetic; the primary reviewer checked and integrated their findings.
The arithmetic implementation was written from the manuscript equations
without importing the original implementation. This is AI-assisted checking,
not independent human refereeing or formal verification. No Lean build or
kernel/axiom audit was performed.

## Correctness findings

| Claim | Finding and scope |
|---|---|
| Arbitrary-orientation coherent-set bound $h+2$ | The fixed-head injection and bucket induction are valid. The arbitrary-orientation sharpness construction works for $q\ge3$. |
| Uniform exact-contract generator | Word capacity, cyclic regularity, palette size, and $O(\log^2 M)$ bit time/$O(\log M)$ storage follow as stated. |
| Six ordinary-zero and five joint-zero branches | No missing candidate case or threshold assumption was found. The exceptional head-label reassignment and stronger-index joint argument are necessary and valid. |
| One-side recurrences, zero-block witnesses, OR and composition | The stated arguments are valid and inherited. They do not constitute the contribution of this note. |
| Published fixed-seed arithmetic | All saved seed integers and certified exponent intervals matched the independently implemented recurrence. |
| Numerical importance | A strict but small improvement in proved upper bounds, with no exact-sensitivity or global-optimality claim. The sharper baseline below must be considered when describing its size. |
| Later literature check | ProveIt Parts I–II (7 and 9 October 2026) report larger exponents and prove the two- and three-gate packing counts; see the [novelty audit addendum](NOVELTY_AUDIT.md#addendum-proveit-manuscripts-located-after-this-audit). |
| Historical novelty | The first-difference mechanism is classical. No exact antecedent was found for the directed lemma or six/five-branch formulation in the inspected sources. Priority remains unresolved. |

For the profile proof, the essential assumptions are nested child predicates,
targets at the strongest child index $Q$, gates at one common index $g<Q$,
distinct children within each clause, a tournament orientation, and a
head-coherence cap. Regularity is used for the stated one-side coefficient
$M^2$. The proof does not assume that a raw bit crosses only one threshold.
Joint profiles count simultaneous transitions of distinct predicates on the
same child input and raw coordinate.

The numerical countermodel in the earlier novelty audit only establishes
nonimplication from a system of one-step scalar inequalities. It is not a
realizable Boolean counterexample, a proof of independence from every lemma
in the source, or a historical novelty certificate. The local candidate
examples likewise do not establish simultaneous sharpness of the full
recursive profiles.

## A direct strengthening of the indexed label construction

Let $q\ge3$, $r=13(q-1)$, $M=r^2$, and $k=2M^2+1$, with the same
cyclic orientation and first-difference labels as the published note. Put
$H=\lceil\log_q k\rceil\le13$.

**Proposition.** Every head-coherent set in this indexed tournament has at
most $H+1$ vertices. Thus fourteen is a uniform bound for this family. At
$q=1001$ the exact maximum is seven.

**Proof.** Delete the $13-H$ common leading zero digits. This subtracts the
same palette offset from all labels and preserves coherence. Within any
fixed prefix of length $H-1$, vertex indices span at most $q-1$. Since

$$q-1\le13^4(q-1)^4=M^2,$$

every edge in such a final-digit bucket points from the smaller to the larger
index. Three distinct one-digit vertices would give the largest vertex two
incoming edges with different source digits. Fixed-head injectivity excludes
this, so the one-digit coherent bound is two.

The published bucket argument applies inside every prefix: there is at most
one nonsingleton first-digit bucket; if it exists there is at most one vertex
outside it; and if all buckets are singletons there are at most three
vertices. Consequently the successive bounds satisfy

$$C_1\le2,\qquad C_s\le\max\{3,C_{s-1}+1\}\le s+1\quad(s\ge2).$$

This proves the upper bound, including the separate base case $H=1$.
For $q=1001$,

$$q^5=1{,}005{,}010{,}010{,}005{,}001
 < M^2=28{,}561{,}000{,}000{,}000{,}000,$$

and $q^5<k<q^6$, so $H=6$. The seven vertices

$$\{0,1,q,q^2,q^3,q^4,q^5\}$$

span less than $M^2$, hence all edges point increasingly. For each head
$q^j$, all earlier vertices agree with it before its leading one and have
zero in that position. Their incoming labels at that head coincide. This is
a coherent seven-set, proving equality. $\square$

The uniform fourteen bound is also attained, at $q=3$, by

$$\{3^{11}\}\;\cup\;\{3^{11}+3^j:0\le j\le10\}
  \;\cup\;\{2\cdot3^{11},3^{12}\}.$$

These fourteen valid indices lie between $177147$ and $531441$, with span
$354294<M^2=456976$. Edges again point increasingly. The successive powers
in the lower suffix, then the leading digit two at place $3^{11}$, then
the one at place $3^{12}$, each give a common first-difference position and
source digit at every head. Thus this is a coherent fourteen-set. This does
not change the sharp $h+2$ statement for arbitrary orientations: the cyclic
indexed family has additional structure.

## The profile formulas with an arbitrary cap

Let $K\ge3$ be an upper bound on the size of every head-coherent set. The
published profile proof gives

$$\begin{aligned}
F_0^{(K)}(a,b,c,e)=\max\{&a+(K-1)c,\ a+(K-2)c+b,\ Kc+e,\\
 &(K-2)c+b+e,\ (K-1)c+2e,\ (K-3)c+3e\},\\
F_J^{(K)}(a,b,c,e)=\max\{&a+(K-1)c,\ a+(K-2)c+e,\ Kc+e,\\
 &(K-1)c+2e,\ (K-3)c+3e\}.
\end{aligned}$$

Here $0\le c\le a$ and $0\le e\le b$ as in the note. To justify the
parameter substitution, the six ordinary cases give target counts at most
$K$, $K-1$, $K$, $K-2$, $K-1$, and $K-3$, respectively. In the first two
cases at most one target costs $a$; the others cost $c$. In the second case
the exceptional ordinary target's incoming label must be reassigned as in
the published proof. In the fifth case at most one exceptional target is
deleted before making the union coherent. The final case uses the coherent
union with three cyclic gate candidates. All other candidate arguments are
independent of the number fifteen. For joint acceptance, form the stronger
parent lists and retain gates that fail at both indices; every retained gate
costs $e$. Substitute $b=e$ in the six cases and discard the fourth branch,
which is dominated by the fifth. This proves the displayed formulas.

The matching immediate source-derived baseline is

$$S_{j,0}\le Ka+\max\{b+e,3e\},\qquad J_{j,0}\le Ka+3e.$$

Both analyses retain $S_{j,1}\le M^2a+rb$ and
$J_{j,1}\le M^2c+rb$, the base vector $(18,19M,0,0)$ for this seed, and
the same definitional caps $J_{j,b}\le S_{j,b}$. All coefficients are
nonnegative, so propagating componentwise upper bounds is valid.

## A comparison using the sharper information on both sides

Keep exactly the published $q=1001$, $d=17$, $M=169000000$, $r=13000$,
$k=57122000000000001$, and $C=164900179$. The Boolean function, OR-copy
count, dimension $n=C\cdot19M(kr)^{17}$, and block lower bound $B=CMk^{17}$
are identical in every row. For each computed sensitivity upper bound $A$,
write $\alpha=\log(B)/\log(A)$.

| Coherence information used | Immediate baseline $\alpha$ | Coupled-profile $\alpha$ |
|---|---:|---:|
| $K=15$, as in the original certificate at `00820a6` | 2.015410903091582180… | 2.015411547311478476… |
| $K=8$, deleting common leading digits only | 2.015411203868314436… | 2.015411547486334582… |
| $K=7$, using the proposition above and now included in the manuscript | 2.015411246837677710… | 2.015411547511314020… |

The decimals in this table are abbreviated, not interval endpoints. Exact
integers and enclosing rational/decimal intervals are saved in
[independent-audit.json](../checks/independent-audit.json).
At $K=7$, the certified gain is approximately
$3.0067363631\times10^{-7}$. The sharper immediate baseline still falls
below the original $K=15$ coupled certificate, by approximately
$3.0047380077\times10^{-7}$. Thus the elementary tightening does not
subsume the published coupled-profile improvement.

The PDF at the reviewed commit `00820a6` remains valid under its explicitly
stated contract. It disclosed that the cap of eight was unused. The current
manuscript includes the sharper comparison above, using the additional easy
information on both sides. Neither comparison claims exact sensitivity, optimal parameters, an
optimal proof bound, or a literature-wide record. The OR-copy count is held
fixed; no new parameter sweep or global optimization was performed.

## What is new relative to the inspected work

| Ingredient | Defensible assessment |
|---|---|
| First differing position plus source symbol | Classical Cole–Vishkin local asymmetry; the larger alphabet is elementary. See [Vishkin's notes, printed p. 72](https://users.umiacs.umd.edu/~vishkin/PUBLICATIONS/classnotes.pdf) and the [1986 article](https://doi.org/10.1016/S0019-9958(86)80023-7). The original publisher full text was not retrieved. |
| Fixed-head compression, parameter arithmetic, and query complexity | Routine consequences of the encoding and lemma. |
| Arbitrary-orientation $h+2$ lemma | A specific directed adaptation requiring the bucket argument. No exact theorem match was located; historical novelty is unresolved. |
| Hypercube first-difference antecedents | [Gishboliner–Milojević–Sudakov–Wigderson, §2.1, Theorem 2.3 proof and Remark 2.5](https://arxiv.org/html/2410.08644v1#S2.SS1), treat binary position-only colors and lexicographic copies. They do not directly state the arbitrary-orientation, source-digit coherence lemma. |
| Star-coloring antecedents | [Lo–Markström–Mubayi–Staden–Stein–Weber, §3.1 and Lemma 3.1](https://homepages.math.uic.edu/~mubayi/papers/star-anti-ramsey-2.pdf), use color classes that are stars and tournament-induced tail colors. Our compressed labels need not form global stars, so that correspondence alone does not prove this bound. |
| Uniform family-132 labels | A deterministic specialization of the source's existence requirement; the Boolean architecture is inherited. |
| Four profiles, candidate lists, $|G|\le3$, internal gate joint repairs | Already in the [source recurrence proof](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex). |
| Most target repairs are joint; coupled union counts; stronger-index joint lists | Additional arguments relative to that proof. These yield the six/five branches; this is the clearest specific refinement contributed by the note. Their simplicity does not establish either prior occurrence or priority. |
| The new $H+1$, fourteen, and exact-seven conclusions | Direct corollaries proved above, not independent methodological innovations. |
| OR balancing and composition | Established. The OR identities appear in [Ambainis–Sun, §4, Lemma 1](https://arxiv.org/html/1108.3494v1); see also [Tal, ITCS 2013](https://doi.org/10.1145/2422436.2422485) for Boolean composition. |

The broader antecedent comparison remains in [NOVELTY_AUDIT.md](NOVELTY_AUDIT.md).
The ordinary/spectral sensitivity distinction remains essential: a lower
bound in terms of spectral sensitivity does not by itself give the claimed
comparison with ordinary sensitivity.

An authenticated GitHub history check filled the earlier audit's access gap.
On 15 October 2026, OpenAI/math HEAD was still the pinned
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`. History queries for both the
family-132 manuscript directory and `lean/docs/132.md` returned only the
initial commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, dated 6 October
2026. Listing all issues and PRs, including closed items, returned PRs
[#1](https://github.com/openai/math/pull/1) and
[#2](https://github.com/openai/math/pull/2), both with zero issue comments.
Issue/PR searches for `sensitivity` and `132` returned zero results. These
checks concern the public repository, not private discussions or all prior
mathematics. Search absence cannot certify novelty.

## Reproduction and verification limits

The published commit was extracted to a fresh temporary checkout with an
empty source cache. Its existing command completed successfully in 34.50
seconds:

```sh
python3 topics/sensitivity-separation/scripts/reproduce.py --fetch-sources
```

It fetched and matched all 63 pinned source hashes, checked 129088 small
labelled tournaments and 46656 local profile configurations, and reproduced
the published certificate. The printed arbitrary-orientation sharpness
example of size fifteen is compatible with the smaller cyclic-family bound.

At the time of this review, the new independent implementation was run
separately with the command below. It is now also included in the main
reproduction command.

```sh
python3 topics/sensitivity-separation/checks/independent_audit.py
```

It matched the saved seed integers, printed enclosures, 373-digit dimension,
coarse certificate, and the two saved scan candidates without rerunning a
scan. It checked the two bracketing baseline OR-copy counts, all 21 pairs in
the seven-vertex witness, and exact inequalities
$A^{20154}<B^{10000}\le A^{20155}$ for both published bounds. The final run
completed in 4.515 seconds, including 4.505 seconds for exact powers.

Unlike the original logarithm implementation, it uses no library logarithm.
For an integer $x$, set $e=\lfloor\log_2 x\rfloor$ and
$z=(x-2^e)/(x+2^e)\in[0,1/3)$. It encloses

$$\log x=e\log2+2\sum_{j=0}^{119}\frac{z^{2j+1}}{2j+1}+R,
\qquad 0\le R\le\frac{2z^{241}}{241(1-z^2)}.$$

The same series with $z=1/3$ encloses $\log2$. Every arithmetic step rounds
outward on the rational lattice $10^{-100}\mathbb Z$, and exponent ratios
use lower numerator/upper denominator and upper numerator/lower denominator.
The resulting intervals lie inside the published enclosures and separate
every reported comparison. The implementation and its rounding argument were
also inspected by the primary reviewer.

These computations corroborate the written proofs. They neither evaluate the
huge truth table nor independently formalize the infinite statements. The
historical claims still need external literature scrutiny. Counterexamples,
missing references, and negative or inconclusive findings are welcome.
