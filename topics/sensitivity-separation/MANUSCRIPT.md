# Succinct first-difference labels for a sensitivity construction

Research manuscript, 15 October 2026. The precise directed adaptation and
application below have provisional novelty status; the underlying
first-difference method is classical.

## Abstract

The family-132 construction of a superquadratic separation between ordinary
sensitivity and block sensitivity uses a labelled regular tournament with
no head-coherent set of 16 vertices. We give an elementary deterministic
replacement for its random-existence labelling. For words of length `h`,
label an edge by its first differing position and the source digit, encoded
injectively relative to the fixed head. Every head-coherent set has at
most `h+2` vertices, for every tournament orientation. Taking `h=13`
produces the exact family-132 parameters on an infinite family, with
`O((log M)^2)` bit time per edge query and no witness advice. The published
Boolean recursion then gives uniformly specified superquadratic examples
and a fixed exponent greater than two by composition. The labelling
theorem alone does not improve the published sensitivity estimates.

## 1. The exact directed condition

A tournament directs exactly one edge between each pair of distinct
vertices. A labelled tournament has a label `a(i,j)` on each directed edge
`i -> j`. A set `I` is **head-coherent** if there is a label `m_j` for every
`j in I` such that

\[
 a(i,j)=m_j\qquad\text{whenever }i,j\in I\text{ and }i\to j.
                                                        \tag{1}
\]

A vertex with no incoming edge inside `I` imposes no constraint on its
chosen label. This is exactly the condition in Lemma 2.1 of the pinned
OpenAI family-132 manuscript [1], with zero-based vertex and label indices.
It is not equivalent to forbidding monochromatic sets or only transitive
coherent sets.

For an integer `M>=3`, that application requires

\[
 k=2M^2+1,\qquad r=\lceil\sqrt M\rceil,
\]

a regular tournament on `k` vertices, of outdegree `M^2`, and labels in
`{0,...,r-1}` for which no 16-set satisfies (1). The source obtains such
labels by independent randomness, using
`k^16 r^(-104) <= 3^16 M^(-20) < 1`. The construction below needs no
randomness, exhaustive witness selection, or stored edge table.

## 2. A first-difference theorem

Let `h>=1` and `q>=2`. Vertices are distinct words
`x=(x_1,...,x_h)` in `{0,...,q-1}^h`, or any subset of those words.
Give them an arbitrary tournament orientation. For `x -> y`, let `u` be
the first position where `x_u != y_u`, and define

\[
 a(x,y)=(u-1)(q-1)+x_u-\mathbf1\{x_u>y_u\}.
                                                        \tag{2}
\]

This uses `h(q-1)` labels. At a fixed head digit `b`, the map
`a -> a-1{a>b}` sends the digits other than `b` bijectively to
`{0,...,q-2}`. Consequently equal labels at one head mean equal
first-difference positions and equal source digits at that position.
Different positions have disjoint label palettes.

**Theorem 1.** Every head-coherent subset under (2) has at most `h+2`
vertices, for every tournament orientation.

**Proof.** Partition a coherent set by its first digit, calling the
parts buckets. A vertex receiving an edge from its own bucket receives
a label with position at least two. It therefore receives no edge from
another bucket, where the position would be one. Such a vertex sends
an edge to every vertex outside its bucket.

Every bucket of size at least two contains a vertex with an incoming
edge from that bucket. If two buckets had size at least two, a chosen
vertex of this kind in each bucket would have to send an edge to the
other, a contradiction. Thus there is at most one bucket `B` of size
at least two.

If `B` exists, choose `z in B` with an incoming edge from `B`. Every
outside vertex receives an edge from `z`, and every outside bucket is
a singleton. If two outside vertices existed, their mutual edge would
give its head two incoming labels at position one with different
source digits: one from `B`, and one from the other outside bucket.
The fixed-head injectivity in (2) excludes this. Hence there is at most
one vertex outside `B`.

If every bucket is a singleton, each vertex has indegree at most one,
since two distinct incoming sources have different first digits.
Summing indegrees gives `|I|(|I|-1)/2 <= |I|`, hence `|I|<=3`.

Within `B`, deleting the common first digit preserves coherence for
the suffix rule, after removing the fixed palette offset. The one-digit
case has size at most three, and the preceding argument gives
`C_h <= max(3,C_(h-1)+1)`. Induction proves `C_h<=h+2`. QED.

For `q>=3`, this bound is sharp for arbitrary orientations. Start with
three words differing only in their last digit, oriented as a directed
triangle. Add one word at a time whose first nonzero digit occurs one
position earlier than all preceding nonzero digits, and direct all
previous vertices toward it. Each added head receives a single label,
giving a coherent set of size `h+2`.

The same proof allows unequal radices, with a palette of `q_u-1` labels
at position `u`. If the last radix is two, its base case has size two,
and the bound is `h+1`. These refinements and finite parameter examples
are recorded in [CONSTRUCTOR.md](proofs/CONSTRUCTOR.md); they are not
needed for the following infinite family.

## 3. Exact parameters and uniform complexity

**Theorem 2.** For every integer `q>=3`, set

\[
 M=[13(q-1)]^2,\quad r=13(q-1)=\lceil\sqrt M\rceil,
 \quad k=2M^2+1.                                      \tag{3}
\]

There is a uniform deterministic regular tournament on `{0,...,k-1}`
with labels in `{0,...,r-1}` and no head-coherent 16-set. An orientation
or label query uses `O(log M)` bits of storage and
`O((log M)^2)` bit operations.

**Proof.** Use the cyclic regular orientation

\[
 i\to j\quad\Longleftrightarrow\quad
 1\le (j-i)\bmod k\le M^2.                            \tag{4}
\]

Exactly `M^2` residues are successors of each vertex. Since `k` is odd,
each unordered pair has exactly one direction.

Encode `i` as exactly 13 base-`q` digits, including leading zeros, and
use (2). There are enough words. At `q=3`,

\[
 k=913953<1594323=3^{13}.
\]

For `q>=4`,

\[
 q^{13}-k
 >q^4(q^9-2\cdot13^4)-1>0,
\]

because `4^9=262144>57122=2*13^4`. The 13 positions use
`13(q-1)=r` labels, and Theorem 1 bounds coherent sets by 15.

All integers in (2)--(4) have `O(log M)` bits. A fixed number of
schoolbook arithmetic operations recovers 13 digits, their first
difference, and the edge orientation, giving the stated conservative
bit bound. The algorithm does not preprocess the vertices or edges.
The family (3) is infinite and unbounded. QED.

The complete executable interface is `SuccinctTournament(q)` in
[label_contract.py](checks/label_contract.py). The parameter is the
integer `q`, not a nonuniform advice string. Admissible `M` also determines
`q` by integer square root and division by 13.

## 4. The ordinary-sensitivity corollary

For a total Boolean function `f:{0,1}^n -> {0,1}`, ordinary sensitivity
`s(f,x)` counts individual coordinates whose flip changes `f(x)`.
Block sensitivity `bs(f,x)` is the largest number of pairwise disjoint,
nonempty coordinate blocks whose separate flips each change `f(x)`.
Write `s(f)=max_x s(f,x)`, `bs(f)=max_x bs(f,x)`, and `bs(f,0)` for
the zero-input quantity.

The remainder of this section is the application of the published
family-132 recursion and bounds [1] to Theorem 2, not a new profile
inequality. Its complete independent audit is in
[VERIFICATION.md](proofs/VERIFICATION.md).

### 4.1. Total nested predicates

Fix a recursion depth `d>=1`, independently of the fixed digit length
`h=13`, and put

\[
 q(d)=\max\left\{3,\ 1+\left\lceil\frac{3^{d+1}}{13}\right\rceil\right\},
 \quad M=[13(q(d)-1)]^2,
 \quad L=d+2.                                         \tag{5}
\]

Then `M>=9^(d+1)`, and (3) supplies `k,r` and the required labels.
For `0<=ell<=d`, define

\[
 H_\ell=d+1-\ell,\qquad N_\ell=LM(kr)^\ell.
\]

Partition the `LM` base coordinates into `M` blocks `E_j` of size `L`.
Let `z_j=1_(E_j)` and `D(x)=min_j dist(x,z_j)`. For predicate indices
`1<=p<=H_0`, define

\[
 P_{0,p}(x)=\mathbf1\{D(x)\le d+1-p\}.
\]

At level `ell>=1`, partition the coordinates into `kr` children
`x_(j,c)`, with vertex rows `0<=j<k` and label columns `0<=c<r`.
Put `Q=H_(ell-1)`. Clause `i` for predicate index `p` requires

\[
 \begin{aligned}
 P_{\ell-1,Q}(x_{i,c})&=1 &&\text{for every }c,\\
 P_{\ell-1,Q-p}(x_{j,a(i,j)})&=0 &&\text{for every }i\to j.
 \end{aligned}                                       \tag{6}
\]

Define `P_(ell,p)` as the OR of these clauses. All indices are valid:
`1<=Q-p<Q`. These formulas define functions on every binary input,
without promises. They are nested in `p`: increasing `p` strengthens
the gate conditions in (6).

All predicates reject zero. At level `ell` there are `Mk^ell` pairwise
disjoint nonempty blocks, each of size `Lr^ell`, whose separate flips
at zero make every level-`ell` predicate accept. At level zero these
are the `E_j`. Inductively, copy one preceding block into all `r`
children of one row and take their union. This satisfies the targets
for that row while leaving every gate row at zero. Distinct row or
block choices stay disjoint. In particular, the predicates are
nonconstant.

### 4.2. The inherited four profiles

Let `S_(ell,b)` be the maximum sensitivity of `P_(ell,p)` over all
indices `p` and inputs where it equals `b`. Let `J_(ell,b)` be the
maximum, over two distinct indices `p<p'` and a **single** input where
both predicates equal `b`, of the number of **single raw bits** whose
flip changes both predicates to `1-b`. Empty maxima are zero, so
`J_(d,0)=J_(d,1)=0`.

The base predicates satisfy

\[
 S_{0,0}\le L,\qquad S_{0,1}\le LM,\qquad J_{0,0}=J_{0,1}=0.
\]

Indeed, the centers have mutual distance `2L`, so a rejecting input
can be one flip from at most one relevant ball. Also `D` is
1-Lipschitz, so one flip cannot cross two distinct integer radii.

The published four-profile theorem gives, with primes denoting the
preceding level,

\[
 \begin{aligned}
 S_0&\le16S'_0+S'_1+3J'_1,& S_1&\le M^2S'_0+rS'_1,\\
 J_0&\le16S'_0+3J'_1,& J_1&\le M^2J'_0+rS'_1.
 \end{aligned}                                       \tag{7}
\]

The label condition enters the zero-to-one estimate by bounding the
clauses with one failed target: their rows form a head-coherent set.
The argument also bounds the one-failed-gate candidate tournament by
three vertices and uses simultaneous threshold crossings for its
joint contributions. Theorem 2 supplies precisely the label hypothesis
of this argument; it introduces no replacement for (7).

For `M>=9^(d+1)`, the published quantitative bound is

\[
 S_{\ell,b}\le2L M^{\ell+b}\qquad(0\le\ell\le d).     \tag{8}
\]

To see the scaling, normalize by `M^(ell+b)`, put
`epsilon=max(r,16)/M<=2/3^(d+1)`, and let `u_ell,v_ell` be the maxima
of the normalized ordinary and joint profiles. Equation (7) gives
`u_ell<=(1+epsilon)u_(ell-1)+3v_(ell-1)` and
`v_ell<=epsilon u_(ell-1)+3v_(ell-1)`. Starting from `u_0<=L,v_0=0`,
simultaneous induction bounds them by `2L` and
`epsilon L(3^ell-1)`, respectively, proving (8).

### 4.3. OR balancing and amplification

Let `f_d` be the OR of `M` disjoint copies of `P_(d,1)`. It is total,
nonconstant, rejects zero, and has dimension

\[
 n=(d+2)M^2(kr)^d.                                    \tag{9}
\]

At a zero input, its sensitivity is at most `M S_(d,0)`. At a one
input, two accepting copies make the OR insensitive; if exactly one
copy accepts, the sensitivity is at most `S_(d,1)`. Its disjoint
zero-block families accumulate across copies. Hence

\[
 s(f_d)\le A=2(d+2)M^{d+1},\qquad
 \operatorname{bs}(f_d,0)\ge B=M^2k^d.                \tag{10}
\]

Thus this **uniformly specified** family has

\[
 \frac{\operatorname{bs}(f_d)}{s(f_d)^2}
 \ge\frac{B}{A^2}
 \ge\frac{2^d}{4(d+2)^2}\longrightarrow\infty.
\]

Fix `d=9` and use (5). Then `A=22M^10` and `B=M^2k^9`, with the
exact strict comparison

\[
 \frac{B}{A^2}\ge\frac{2^9}{484}=\frac{128}{121}>1.
\]

For this fixed seed, let `alpha=log(B)/log(A)>2`. Disjoint composition
satisfies `s(f o g)<=s(f)s(g)`. When `g(0)=0`, Cartesian products of
disjoint nonempty zero-sensitive blocks show
`bs(f o g,0)>=bs(f,0)bs(g,0)`. Consequently the `m`-fold seed iterate
`F_m` has dimension `n^m`, rejects zero, is total and nonconstant, and
satisfies

\[
 s(F_m)\le A^m,\qquad
 \operatorname{bs}(F_m,0)\ge B^m\ge s(F_m)^\alpha.
                                                        \tag{11}
\]

Its block sensitivity grows without bound. The exponent in (11) is
the published composition corollary with an explicit choice of labels;
no stronger exponent follows solely from the present generator.

### 4.4. Description and construction cost

Equations (2)--(6) specify each seed by the integers `(d,q)` and fixed
code: `O(log d+log q)` parameter bits, with no tournament advice. If an
independently chosen OR-copy count `c` is supplied, the descriptor uses
`O(log d+log q+log c)` bits; here the count is the derived value `M`. With
the choice (5), `log M=O(d)`, `log n=O(d^2)`, and `q` can instead be
derived from `d`; the variable-length parameter description is then
just `O(log d)` bits. Computing those derived large integers still takes
time polynomial in `d`, not necessarily polynomial in `log d`.

Succinct edge access should be distinguished from evaluation on an
entire `n`-bit Boolean input. A direct evaluator computes all predicate
values at each child once and passes their vector upward. The number
of nodes is `O(n)`. At one internal node there are at most
`d k(r+M^2)=O(d k^2)` target/gate tests, each obtainable with arithmetic
on `O(log n)`-bit integers. Base distances can be computed by scanning
each leaf input once, using
`D(x)=weight(x)+L-2 max_j weight(x restricted to E_j)`.
A conservative overall bound is

\[
 O\bigl(n d k^2(\log n)^2\bigr)
\]

bit operations and `O(n(d+1))` bits for the input and stored predicate
values. Loop counters and recursion bookkeeping also fit this coarse
space bound. This gives a polynomial bound for expanding an evaluation
circuit. It does not require or
imply a truth table of size `2^n`. No such expansion is performed by
the supplied edge-query and diagnostic program.

## 5. Verification and historical scope

The induction in Theorem 1 proves the infinite-family claim. Bounded
diagnostics in `checks/label_contract.py` independently reconstruct
the fixed-head label encoding and exhaust all 129088 relevant small
tournaments: every orientation of the binary two-digit cube, and
every orientation of every five-subset of the ternary two-digit cube.
They also check a sharp coherent 15-set, exact parameter inequalities,
small cyclic regularity, and representative large-index queries.
The serial run passed in 1.826 seconds; no large tournament was
materialized. An independent reviewer checked the saved proof and
implementation. This is a written proof with executable diagnostics,
not a Lean formalization.

First-difference coloring is classical. Cole--Vishkin deterministic
coin tossing uses the position of a differing bit together with a
vertex's own bit [3,4]. Modern canonical Ramsey work also uses the
standard first-difference coloring [5]. The substantive claim to be
assessed historically is the arbitrary-orientation head-coherence
bound and its exact succinct family-132 instantiation. The source
audit did not locate that precise result, but does not establish
priority; see [LITERATURE.md](sources/LITERATURE.md).

Meiburg's related gated-tournament work [2] concerns block sensitivity
versus spectral sensitivity `lambda`. Because `lambda<=s`, a lower
bound in terms of `lambda` does not imply the ordinary-sensitivity
bound (11). We claim no invention of gated tournaments, OR balancing,
composition amplification, or the underlying first-difference
technique.

A separate companion investigation,
[PROFILE.md](proofs/PROFILE.md), studies stronger profile estimates.
Its coefficients and any numerical consequences are not used in this
manuscript's label theorem or the inherited corollary (7)--(11).

To reproduce the bounded diagnostics, from this manuscript's directory:

```sh
python3 checks/label_contract.py --self-test
```

## 6. Companion structural improvement and fixed seed

The companion proof in [PROFILE.md](proofs/PROFILE.md), independently audited,
goes beyond solving (7). Writing A=S0', B=S1', C=J0', D=J1', it proves

\[
\begin{aligned}
S_0&\le\max\{A+14C,A+13C+B,15C+D,13C+B+D,14C+2D,12C+3D\},\\
J_0&\le\max\{A+14C,A+13C+D,15C+D,14C+2D,12C+3D\}.
\end{aligned}
\]

The one-side bounds in (7) remain unchanged. The main new invariant is
that an incoming passing candidate gate at a failed target forces its
weaker child predicate to be zero too. Repairing the strongest predicate
therefore crosses both thresholds. At most one target lacks such an
incoming constraint; when at least two gate candidates exist, none does.
The complete proof handles the exceptional source-head label reassignment
and simultaneous parent acceptance using stronger-index candidate lists.

For the explicit labels at q=1001, set d=17 and take c=164900179 OR copies.
Then M=169000000, r=13000, k=57122000000000001 and

\[
n=c\,19M(kr)^{17},\qquad B=cMk^{17}.
\]

This n has 373 decimal digits. On this same seed, iterating the existing
proof with its immediate refinements gives exponent
2.0154109030915821803..., while the new inequalities give
2.0154115473114784763.... The sensitivity bound decreases strictly at
unchanged B,n. Both exponents exceed 2.0154 by exact integer-power checks;
70-digit enclosing intervals certify the displayed comparison. This is a
strict improvement of a proved bound, not knowledge of the seed's exact
sensitivity or a claim of an optimal exponent. The full recurrence applies
for M>=3 with good labels; the coarse M>=9^(d+1) sufficient condition used
for (8) is unnecessary for this exact iteration.

The baseline, all exact integers, and interval construction are recorded in
[BASELINE.md](proofs/BASELINE.md) and
[seed-certificate.json](checks/seed-certificate.json). A single full
reproduction command, from this manuscript's directory, is

```sh
python3 scripts/reproduce.py --fetch-sources
```

This validates pinned sources and runs all bounded checks serially. It
constructs no large tournament and no Boolean truth table. The structural
result does not alter the independent label proof in Theorems 1–2.

## References

1. OpenAI math family 132, *A superquadratic separation between
   sensitivity and block sensitivity*, 25 September 2026, pinned
   revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
   [Manuscript sources](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026).
2. Alexander Meiburg, arXiv:2608.00851v1, 1 August 2026.
   [Paper](https://arxiv.org/html/2608.00851v1).
3. R. Cole and U. Vishkin, *Deterministic coin tossing with
   applications to optimal parallel list ranking*, Information and
   Control 70 (1986).
   [DOI](https://doi.org/10.1016/S0019-9958(86)80023-7).
4. U. Vishkin, lecture notes, p. 72, position-plus-own-bit formulation.
   [Notes](https://users.umiacs.umd.edu/~vishkin/PUBLICATIONS/classnotes.pdf).
5. L. Gishboliner, A. Milojević, B. Sudakov, and Y. Wigderson,
   arXiv:2410.08644v1, proof of Theorem 2.3.
   [Paper](https://arxiv.org/html/2410.08644v1).
