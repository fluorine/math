# Novelty audit: first-difference labels and coupled sensitivity profiles

Audit date: **15 October 2026**. This is a companion to the
[research note](sensitivity-note.tex), the
[label proof](../proofs/CONSTRUCTOR.md), and the
[profile proof](../proofs/PROFILE.md).

**Follow-up:** the [fresh review and addendum](FOLLOWUP_REVIEW.md) proves the
cyclic-family cap $H+1$ and the exact fixed-seed cap seven, applies that
information to both numerical analyses, and records a separate arithmetic
implementation. It also completes the public GitHub history/issue check
that was access-limited during this audit. The original PDF comparison and
its limitations below are retained as a record of the reviewed version.

**The defensible contribution is an elementary directed adaptation of a
classical labelling method, together with a stronger local estimate for an
existing Boolean-function construction.** The first-difference mechanism is
classical. The specific arbitrary-orientation coherence bound and the
six/five-branch profile inequalities were not located in the sources checked.
The latter inequalities are strictly stronger than the published scalar
recurrences, including their immediate refinements. Their historical priority
remains unresolved. The numerical threshold greater than 2.0154 already
follows from the earlier argument and is not a new separation claim.

Throughout, “the source” means OpenAI's *A superquadratic separation between
sensitivity and block sensitivity*, dated 25 September 2026, at commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Its family number is 132.
The comparison is with that exact source, rather than with only the coarse
bound highlighted in its main theorem.

## 1. Classification of the claims

| Ingredient or conclusion | Classification | Precise boundary |
|---|---|---|
| Encode vertices as words and use a first differing coordinate | Classical method | Standard first-difference and product-colouring constructions already do this. |
| Record the differing coordinate together with the source symbol | Classical local-asymmetry mechanism | The binary form is the Cole–Vishkin deterministic-coin-tossing mechanism. The extension to a larger alphabet is elementary. |
| Omit the head's digit from the local palette | Routine encoding | This is a bijective relabelling at each fixed head. It preserves exactly the equalities needed for coherence; it does not preserve all global colour relations. |
| Every coherent set has at most $h+2$ vertices under any tournament orientation | Specific lemma proved here; no exact prior theorem located | It requires an additional induction on first-digit buckets. It should be described as an elementary directed adaptation, with provisional novelty. |
| Mixed radices, the $h+1$ bound when the last radix is two, and an arbitrary-orientation sharpness example | Direct variants of that lemma | These are short consequences of the same proof, not separate methodological contributions. Cyclic-family sharpness is addressed separately in the follow-up addendum. |
| The cyclic regular tournament on $2M^2+1$ vertices | Inherited | This orientation is already explicitly proposed in the source, Section 2. |
| The family $M=[13(q-1)]^2$, with an efficient edge-query algorithm | Application of the directed lemma | The parameter choice and arithmetic are routine once the lemma is available. The useful consequence is a uniform deterministic replacement for the source's probabilistic labels on this unbounded family. |
| Nested predicates, four ordinary/joint profiles, and the disjoint blocks at zero | Inherited construction | These are the definitions and arguments in source Section 2. |
| Base bound $S_{0,0}\le d+1$, coefficient 15, the refined gate envelope, and $J_b\le S_b$ | Direct consequences of existing work | All follow immediately from the source's proof or the definitions. They are included in the baseline. |
| Six branches for the next $S_0$ bound and five for the next $J_0$ bound | Additional structural estimate relative to the source | The proof identifies joint target repairs, couples target and gate counts, and changes the candidate-list argument for joint zero transitions. The inequalities do not follow from the earlier scalar inequalities alone. |
| OR balancing, composition amplification, and optimizing the number of OR copies | Existing method and routine optimization | These steps are not novelty claims. |
| A certified exponent above 2.0154 | Consequence of the earlier proof with better parameter analysis | The source-derived baseline already certifies this threshold. |
| A smaller sensitivity upper bound at identical labels, parameters, block bound, and dimension | Quantitative consequence of the new profile estimate | This is a strict, modest comparison of certified bounds. It is not a computation of the seed's exact sensitivity or a record claim. |

## 2. What the generator adds to classical first-difference methods

### Exact object being bounded

A set $I$ in an edge-labelled tournament is **head coherent** if each vertex
$y\in I$ has a label $m_y$ such that every edge $x\to y$ within $I$ has
label $m_y$. A vertex with no incoming edge imposes no condition. The source's
Lemma 2.1 requires the absence of a head-coherent set of size 16. The
condition applies to every induced tournament, including directed cycles.
It is stronger than checking only transitive subsets, and it differs from
requiring all edges of a set to have one common colour.
See [source Lemma 2.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/01-construction.tex#L27).

Let the vertices be distinct words with radices $q_1,\ldots,q_h\ge2$.
For $x\to y$, let $u$ be the first differing coordinate. The raw label is

$$
\widetilde a(x,y)=(u,x_u).
$$

The implemented label is

$$
a(x,y)=\sum_{v<u}(q_v-1)+x_u-\mathbf 1\{x_u>y_u\}.
$$

For a **fixed head** $y$, the map from a permitted raw label to its
implemented value is injective: the position palettes are disjoint, and
deleting $y_u$ from the ordered digits gives a bijection onto
$\{0,\ldots,q_u-2\}$. Therefore

$$
a(x,y)=a(z,y)
\quad\Longleftrightarrow\quad
\widetilde a(x,y)=\widetilde a(z,y).
$$

The raw and implemented labellings have exactly the same coherent subsets.
The reduction in the alphabet is an encoding improvement, not a second
combinatorial theorem.

### Cole–Vishkin: the mechanism is already known

Cole and Vishkin's deterministic coin tossing records a differing bit
position and the source's bit. Vishkin's own exposition gives this ordered
pair on printed page 72. The original article is Richard Cole and Uzi
Vishkin, *Deterministic coin tossing with applications to optimal parallel
list ranking*, **Information and Control 70** (1986), 32–53.
See [Vishkin's lecture notes, p. 72](https://users.umiacs.umd.edu/~vishkin/PUBLICATIONS/classnotes.pdf)
and the [original article DOI](https://doi.org/10.1016/S0019-9958(86)80023-7).
The publisher's full text was not retrieved in this audit; the local
mechanism was checked in the author's exposition.

For the raw labels, consecutive directed edges $x\to y\to z$ cannot
both have label $(u,a)$: the first would require $y_u\ne a$, while the
second would require $y_u=a$. This is the familiar local-asymmetry
argument. It does not by itself prove the $h+2$ coherence bound.

That global walk-colouring property must not be transferred to the
compressed labels. For example, with one ternary digit, the edges
$1\to0$ and $0\to2$ both receive compressed label 0. Compression here
preserves equalities at one head, which is exactly what the application
needs.

### The additional argument is the bucket induction

The new proof obligation is a uniform bound depending on the number of
positions, rather than on the alphabet sizes. In a coherent set, partition
the words by their first digit. Any vertex receiving an edge within its
bucket must dominate every other bucket, because an external incoming edge
would use a different position palette. Consequently at most one bucket
can have more than one vertex. If such a bucket exists, fixed-head
injectivity permits at most one vertex outside it. If every bucket is a
singleton, every indegree is at most one and there are at most three
vertices. Deleting the common first digit in the large bucket gives

$$
C(q_1,\ldots,q_h)
\le \max\{3,1+C(q_2,\ldots,q_h)\},
\qquad C(q_h)\le\min(q_h,3).
$$

This proves $C\le h+2$, and $C\le h+1$ when $q_h=2$. The proof is
short and elementary; its scope over arbitrary orientations is the
specific lemma being contributed. No exact statement or direct cited
corollary giving this bound was located in the comparisons below.

### Other close antecedents and the reductions they do support

| Primary source and locator | Connection and limit of the comparison |
|---|---|
| Gishboliner–Milojević–Sudakov–Wigderson, *Canonical Ramsey numbers of sparse graphs*, arXiv:2410.08644v1, Section 2.1, proof of Theorem 2.3 and Remark 2.5. [Full text](https://arxiv.org/html/2410.08644v1) | The proof uses the standard binary hypercube colouring by first differing coordinate; Remark 2.5 discusses weakly lexicographic colourings. Those ordered, undirected configurations do not cover all head-coherent tournament orientations. Moreover, with one nonbinary coordinate, colouring only by position makes all $q$ vertices coherent. Source digits are essential for the alphabet-independent bound used here. |
| Lo–Markström–Mubayi–Staden–Stein–Weber, *Rainbow subgraphs of star-coloured graphs*, arXiv:2511.12505, Section 3.1 and Lemma 3.1. [Author PDF](https://homepages.math.uic.edu/~mubayi/papers/star-anti-ramsey-2.pdf) | Their orientable colouring assigns an edge its tail vertex's colour. A coherent subset with our **raw** labels becomes such a colouring after reversing the tournament and relabelling the used colours by their heads. The known colour-count bound gives a bound involving the raw palette size; the coordinate-dependent $h+2$ bound still needs the bucket argument. |
| Fox–Grinshpun–Pach, *The Erdős–Hajnal conjecture for rainbow triangles*, Definition 1.2 and Section 2, especially Lemmas 2.2–2.3. [Author PDF](https://www.renyi.hu/~pach/publications/gallaicoloring031113.pdf) | Lexicographic products and first-position colouring architectures are established. The statistics in those lemmas concern globally permitted colour sets and product constructions, rather than per-head coherence in an arbitrary tournament. They do not state the additive bucket bound used here. |
| Girão–Illingworth–Michel–Savery–Scott, *Flashes and Rainbows in Tournaments*, introduction, printed p. 2. [Author PDF](https://people.maths.ox.ac.uk/scott/Papers/flashesrainbows.pdf) | The paper discusses earlier word constructions for monochromatic and rainbow directed paths, including Lefmann–Rödl–Thomas. These constrain paths, rather than all incoming edges at every vertex of a complete induced subgraph. |
| Chaiken, *A Theory for Coloring Walks in a Digraph*, arXiv:2407.06299v1, abstract and Section 1. [Paper](https://arxiv.org/pdf/2407.06299v1) | This provides a broader walk-colouring context for Cole–Vishkin-type constructions. The inspected statements do not supply the head-coherent-clique bound. |

For completeness, the star-colouring reduction in the table is exact.
Two vertices with nonempty incoming stars cannot have the same raw head
label $(u,a)$: both have digit different from $a$ at position $u$, so
the edge between them cannot carry that label. Thus each nonempty raw
colour class on a coherent subset is a single incoming star with its own
head. Reversing the edges gives the orientable colouring. Counting at
least $|I|-1$ colours then yields only
$|I|\le1+\sum_u q_u$ from the full raw palette. The hierarchical
restriction on where the first difference occurs is what yields the
stronger $h+2$ bound.

These comparisons establish antecedents and explicit differences in
hypotheses and conclusions. They do not prove that the directed lemma has
never appeared under another formulation.

### What follows once the lemma is available

Take $h=13$, $q\ge3$, and

$$
M=[13(q-1)]^2,\qquad r=13(q-1),\qquad k=2M^2+1.
$$

There are at least $k$ words of length 13 over $q$ symbols. The cyclic
orientation has outdegree $M^2$, and the lemma excludes coherent
16-sets using exactly $r=\lceil\sqrt M\rceil$ labels. The arithmetic
proof and the conservative $O((\log M)^2)$ bit-time, $O(\log M)$
space bounds are direct consequences of the formula; no separate
algorithmic breakthrough is claimed. The resulting useful improvement
over source Lemma 2.1 is **uniform deterministic edge access on an
unbounded parameter family**, with no stored edge table, random seed, or
nonuniform witness advice. It does not provide all integers $M\ge3$,
nor logarithmic-time evaluation of the entire Boolean function.

## 3. What the stronger profile theorem adds

### Definitions and the complete existing baseline

At a fixed child level, write

$$
a=S_0,\quad b=S_1,\quad c=J_0,\quad e=J_1.
$$

The ordinary profiles $S_b$ maximize the number of raw-bit flips changing
one predicate from $b$ to $1-b$. The joint profiles $J_b$ maximize flips
changing two distinct nested predicates on the **same input** in that
direction. In particular, $0\le c\le a$ and $0\le e\le b$.
Write a superscript $+$ for the parent level. Source Proposition 3.1 gives

$$
\begin{aligned}
S_0^+&\le16a+b+3e,& S_1^+&\le M^2a+rb,\\
J_0^+&\le16a+3e,& J_1^+&\le M^2c+rb.
\end{aligned}
$$

The inequalities and their proof are in
[source Section 3, Proposition 3.1](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex#L8).
They hold for $M\ge3$ with the required labels. The later condition
$M\ge9^{d+1}$ belongs to the coarse quantitative Lemma 4.1, not to
this four-profile recurrence. Applying the full recurrence outside that
coarse regime is therefore existing-formula analysis.

The following refinements are immediate from the existing proof and are
credited to it in our comparison:

1. **Initial zero profile.** The proof of source Lemma 2.2 explicitly
   counts at most $R+1\le d+1$ flips. Its displayed $d+2$ bound can
   therefore be replaced by $d+1$.
2. **Target count.** The source proves $|T|<16$ before charging $16a$.
   The charge can immediately be replaced by $15a$.
3. **Gate envelope.** The source proves $|G|\le3$, and every vertex
   with an internal outgoing edge has joint gate cost at most $e$.
   For one or two gate candidates the cost is at most $b+e$; three
   candidates form a cycle and cost at most $3e$. Hence the ordinary
   gate contribution is at most $\max\{b+e,3e\}$.
4. **Definitional caps and final level.** Always impose $J_b\le S_b$.
   When only one predicate remains, both joint profiles are zero by
   the empty-maximum convention.

Thus the source-derived zero-side baseline used in the fixed comparison is

$$
S_0^+\le15a+\max\{b+e,3e\},\qquad
J_0^+\le15a+3e,
$$

with the source's one-side inequalities unchanged. These improvements
require no new invariant. The relevant locators are
[Lemma 2.2 and its proof](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/01-construction.tex#L142),
[the target count](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex#L70),
and [the gate argument](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex#L82).

### The additional local information

At a zero input, $T$ consists of clauses with one failed target and no
failed gate; $G$ consists of clauses with one failed gate and no failed
target. The source already introduces these lists and proves that they
cover every successful flip. The additional proof establishes:

- All but at most one target candidate must cross both the gate threshold
  and the strongest child threshold, so their cost is $c$, rather than
  merely $a$. The possible exceptional target is a source of the
  tournament induced by $T$.
- Every vertex of $G$ dominates every vertex of $T$. Two or more gate
  candidates rule out an exceptional ordinary target.
- The allowable number of targets depends on the number and type of gate
  candidates. In the one-gate case with an ordinary target, the head label
  at that source must be reassigned when testing coherence of $T\cup G$.
  In the two-joint-gate case, removing at most one exceptional target
  makes the union coherent.

These facts give the following six possibilities; costs refer to the
number of candidate repair coordinates, bounded by a union bound.

| Gate candidates | Additional condition | Upper bound on repair cost |
|---:|---|---:|
| 0 | At most one ordinary target | $a+14c$ |
| 1 | An ordinary target or an ordinary gate exists | $a+13c+b$ |
| 1 | Neither ordinary type exists | $15c+e$ |
| 2 | The sink gate is ordinary | $13c+b+e$ |
| 2 | Both gates are joint | $14c+2e$ |
| 3 | The three vertices form a directed cycle | $12c+3e$ |

For joint zero transitions, the source starts with candidate lists at the
weaker parent index. The new proof instead starts at the **stronger**
parent index and retains gate candidates whose failed gate is also failed
at the weaker index. Every simultaneous successful flip is covered by
these lists: otherwise a clause with all targets true and all weaker
gates passing would make the weaker parent initially one. Each retained
gate repair now crosses two distinct gate thresholds and has cost $e$,
including an ordinary gate. This change is necessary to apply the same
joint-target and coupled-counting argument to $J_0^+$.
Compare [the source's joint-zero argument](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex#L115)
with [the complete new proof](../proofs/PROFILE.md#joint-zero-transitions).

The resulting theorem is

$$
\begin{aligned}
S_0^+&\le\max\{a+14c,\ a+13c+b,\ 15c+e,\
                  13c+b+e,\ 14c+2e,\ 12c+3e\},\\
J_0^+&\le\max\{a+14c,\ a+13c+e,\ 15c+e,\
                  14c+2e,\ 12c+3e\},\\
S_1^+&\le M^2a+rb,\qquad
J_1^+\le M^2c+rb.
\end{aligned}
$$

For actual profiles, $c\le a$ and $e\le b$ show branch by branch that
these zero-side envelopes are no larger than the source-derived baseline.
They can be strictly smaller. This is additional analysis of exactly the
source construction and hypotheses; the gated architecture and the idea
of tracking joint sensitivity are inherited.

### A precise scalar nonimplication witness

The claim that more than scalar recurrence optimization is being done can
be checked without any numerical search. Set

$$
M=3,\quad r=2,\quad(a,b,c,e)=(1,1,0,0),
\qquad(S_0^+,S_1^+,J_0^+,J_1^+)=(3,11,2,2).
$$

All entries are nonnegative, and the child and parent definitional caps
hold: $0\le1$, $0\le1$, $2\le3$, and $2\le11$.
The four bounds evaluate as follows.

| Parent quantity | Chosen value | Source displayed upper bound | Source plus immediate refinements | New upper bound |
|---|---:|---:|---:|---:|
| $S_0^+$ | 3 | $16+1=17$ | $15+\max(1,0)=16$ | $\max(1,2,0,1,0,0)=2$ |
| $S_1^+$ | 11 | $9+2=11$ | 11 | 11 |
| $J_0^+$ | 2 | 16 | 15 | $\max(1,1,0,0,0)=1$ |
| $J_1^+$ | 2 | $0+2=2$ | 2 | 2 |

Thus these numbers satisfy the earlier inequalities, including the
immediate refinements and $J_b\le S_b$, while violating both new
zero-side bounds. The new estimates cannot be obtained by algebraic
manipulation of that scalar system alone.

This is an **abstract countermodel to implication between inequalities**.
It is not asserted to be a realizable profile of Boolean predicates, a
reachable level of the recursive construction, or a counterexample to
the source's mathematical theorem. In fact the structural theorem
precludes its realization under the construction's full hypotheses.

## 4. What the quantitative improvement does and does not establish

The comparison fixes a single explicit Boolean seed, using

$$
q=1001,\quad d=17,\quad M=169000000,\quad r=13000,\quad
k=57122000000000001,
$$

and $164900179$ disjoint OR copies. Its dimension and zero-block lower
bound are, respectively,

$$
n=164900179\cdot19\cdot M(kr)^{17},\qquad
B=164900179\cdot M k^{17}.
$$

The integer $n$ has 373 digits. Both analyses use the same explicit
labels, the same function, the same $B$, and the same $n$. Only the
proved sensitivity upper bound $A$ changes.

| Analysis of this same seed | Certified $\log B/\log A$, shortened for display |
|---|---:|
| Source argument with the listed immediate refinements | $2.015410903091582180\ldots$ |
| New coupled-profile theorem | $2.015411547311478476\ldots$ |

The gain is approximately $6.4422\times10^{-7}$ in the certified
exponent. Exact integers establish $A_{\rm new}<A_{\rm old}$; with
$B>1$ and $A_{\rm old}>A_{\rm new}>1$, this already proves the
strict exponent comparison. Disjoint enclosing intervals and exact
integer-power checks are saved in
[seed-certificate.json](../checks/seed-certificate.json). Neither number
is asserted to use the seed's exact sensitivity. No global or sampled
optimum is certified.

There is a further direct consequence of **our label theorem** that these
calculations deliberately leave unused. Here $k<1001^6$, so all thirteen-digit
indices share seven leading zeros. Deleting them and subtracting the common
label offset gives six varying positions, hence a coherent-set bound of eight.
The source's target-count argument can exploit this stronger bound too.
Both displayed calculations instead use only the common no-coherent-16
contract. Their strict comparison isolates the coupled-profile refinement
under that contract; neither is an optimized analysis of the actual seed.
This label-specific sharpening should not be presented as another independent
structural theorem.

The steps that turn these bounds into an infinite family are inherited:

- Ambainis–Sun, Section 4, Lemma 1, already gives the exact identities
  $s_0(\operatorname{OR}_m\circ g)=m s_0(g)$,
  $s_1(\operatorname{OR}_m\circ g)=s_1(g)$, and
  $bs_0(\operatorname{OR}_m\circ g)=m bs_0(g)$ for disjoint copies.
  Here $bs_0$ denotes the maximum over inputs where the function is zero;
  our particular all-zero witness family is inherited from source Lemma 2.3.
  Choosing the best integer $m$ near the balancing ratio is routine.
  See [arXiv:1108.3494v1, Section 4](https://arxiv.org/pdf/1108.3494v1).
- The source itself proves the composition estimates
  $s(f\circ g)\le s(f)s(g)$ and, when $g(0)=0$,
  $bs(f\circ g,0)\ge bs(f,0)bs(g,0)$, then derives a fixed exponent
  greater than two. See [source Lemma 4.2 and Corollary 4.3](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/03-separation.tex#L160).

In particular, an announcement of “a separation with exponent greater
than 2.0154” as the new mathematical achievement would overstate this
work: the source-derived baseline already exceeds that number. The
quantitative contribution is the strictly stronger estimate for an
identical seed, arising from the new local theorem.

The earlier gated-tournament work of Meiburg is also relevant to
attribution. Its headline comparison is between block sensitivity and
**spectral** sensitivity $\lambda$, rather than ordinary sensitivity
$s$. Since $\lambda\le s$, a lower bound in terms of
$\lambda^\alpha$ does not give the corresponding lower bound in terms
of $s^\alpha$. The source explicitly adapts that architecture while
introducing the ordinary/joint profiles used here. See
[Meiburg, arXiv:2608.00851v1, Sections 3.1 and 5.2–5.5](https://arxiv.org/html/2608.00851v1)
and [the source's construction attribution](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/01-construction.tex#L23).

## 5. Publication wording supported by this audit

A suitable contribution statement is:

> We give a directed adaptation of classical first-difference labelling
> and prove an arbitrary-orientation bound for head-coherent subsets.
> This supplies a uniform deterministic replacement for the probabilistic
> labels in the family-132 sensitivity construction on an unbounded
> parameter family. We also refine its ordinary/joint sensitivity
> estimates by counting joint target repairs and coupling target and gate
> candidates. The resulting bounds improve the certified exponent for a
> fixed explicit seed by about $6.44\times10^{-7}$. The underlying
> construction, OR balancing, and composition amplification are inherited;
> the numerical threshold greater than 2.0154 already follows from the
> earlier argument.

This supports a modest technical note with full proofs, source attribution,
and reproducible arithmetic. It does not support claiming invention of
first-difference colouring, a new separation architecture, the first
superquadratic separation, a record exponent, or established historical
priority for the directed lemma. Whether the added lemmas meet a particular
journal's novelty threshold would require an editor's and human referees'
judgment.

## 6. Search scope, versions, and remaining uncertainty

The audit combined primary-source searches with explicit comparisons of
definitions and proofs. Searches covered the source paper and family 132;
ordinary versus spectral sensitivity; explicit labelled tournaments;
first-difference and Cole–Vishkin constructions; canonical, weakly
lexicographic, and star colourings; and directed monochromatic/rainbow
paths. Representative queries included:

```text
"first differing" "tournament"
"first difference" "lexicographic" coloring Ramsey
"tournament" "in-canonical" coloring
"tournament" "locally monochromatic" coloring
"head" "monochromatic" "tournament" labelling
canonical Ramsey tournament incoming monochromatic lexical coloring
"Cole" "Vishkin" "Deterministic coin tossing"
"Rainbow subgraphs of star-coloured graphs"
"ordinary sensitivity" "profile" tournament
"superquadratic separation" "sensitivity"
"BS_Lam" "generator"
```

The source pin was checked against the remote HEAD. The current raw
`01-construction.tex`, `02-recurrences.tex`, and `lean/docs/132.md` were
also compared with their pinned copies on the audit date and were byte
identical. The downloaded source inventory and hashes are in
[sources/manifest.json](../sources/manifest.json). Meiburg's arXiv record
showed version 1; the inspected `Timeroot/BS_Lam` revision was
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`, dated 28 August 2026.
See the [source inventory and earlier search log](../sources/LITERATURE.md).

Coverage of public repository discussion and history was incomplete.
The open-issues landing page showed zero open issues, the Discussions URL
returned 404, and GitHub API rate limits prevented a complete audit of
closed issues and commit history. Neither those observations nor the
absence of matching web results establishes priority. Unindexed work,
unpublished notes, equivalent formulations, and direct consequences of
sources not examined remain possible.

The note has written mathematical proofs, independent AI-agent review,
finite regression checks, and exact arithmetic certificates. It has not
been peer-reviewed by human referees, and these new results have not been
formalized or compiled in Lean. The finite checks support the implementation
and calculations; the written proofs establish the infinite statements.
