# A uniform first-difference labelling

Status: proved elementary construction; the historical novelty of the precise
directed formulation remains subject to the literature audit. The use of digit
words and first differences is classical. No random seed, witness search, table
of edge labels, or unproved pseudorandomness assertion is used below.

## The combinatorial theorem

Let `h >= 1` and let `q_1,...,q_h >= 2` be integers. Vertices are distinct
words in

\[
 X=\prod_{u=1}^h\{0,\ldots,q_u-1\}.
\]

An arbitrary subset of `X` can be given **any tournament orientation**. Define
`R = sum_u (q_u-1)` and `b_u = sum_{v<u}(q_v-1)`. For an edge `x -> y`,
let `u` be the first position where `x_u != y_u` and put

\[
 a(x,y)=b_u+x_u-\mathbf 1\{x_u>y_u\}\in\{0,\ldots,R-1\}.       \tag{1}
\]

For a fixed head digit `y_u`, the map
`x_u -> x_u - 1{x_u>y_u}` is a bijection from the other `q_u-1` digits onto
`{0,...,q_u-2}`. Thus equality of labels at a **fixed head** means equality
of both the first-difference position and the source digit at that position.
The numerical label need not identify the source digit without knowing the
head; the proof never requires that stronger property.

**Theorem 1.** Every head-coherent subset of this labelled tournament has at
most `h+2` vertices. If the last radix is `q_h=2`, the bound improves to
`h+1`.

Here head-coherent has exactly the family-132 meaning: there exist labels
`m_y` such that `a(x,y)=m_y` for every edge `x -> y` inside the subset.
A vertex with no incoming edge places no restriction on its assigned label.

### Proof

In a head-coherent set `I`, partition vertices by their first digit. Call
these parts buckets.

1. If a vertex has an incoming edge from its own bucket, that edge has
   first-difference position at least two. Consequently it has **no**
   incoming edge from another bucket, whose position would be one. Such a
   vertex therefore sends an edge to every vertex outside its bucket.

2. Every bucket containing at least two vertices contains a vertex with an
   incoming edge from its own bucket. If two buckets both had at least two
   vertices, choose such a vertex from each. Step 1 would require both
   directions of the edge between them. Hence at most one bucket contains
   at least two vertices.

3. Suppose that large bucket `B` exists, and choose `z` in it with an
   incoming edge from its own bucket. Every vertex outside `B` receives
   an edge from `z`. All outside buckets are singletons by step 2. If
   two outside vertices `u,v` existed, they would have distinct first
   digits, both different from that of `B`. Whichever way their mutual
   edge is directed, its head would receive one edge from `z` and one
   from the other outside vertex. At this head both labels have
   first-difference position one but different source digits. The
   fixed-head injectivity of (1) contradicts coherence. Thus there is at
   most one vertex outside `B`.

4. If every bucket is a singleton, each vertex has indegree at most one
   inside `I`, again by fixed-head injectivity. Summing indegrees gives
   `|I|(|I|-1)/2 <= |I|`, so `|I| <= 3`.

Inside `B` delete the common first digit. The induced tournament retains
the same coherence property for the suffix labelling, with a constant
palette offset removed. For one digit, all buckets are singletons, so the
bound is `min(q_1,3)`. For more digits, steps 3 and 4 give

\[
 C(q_1,\ldots,q_h)
 \le\max\{3,\ 1+C(q_2,\ldots,q_h)\}.
\]

Induction yields `C <= h+2`. When `q_h=2`, the base bound is two and the
same induction yields `C <= h+1`. This proof makes no assumption that
the orientation is transitive or cyclic. It deals with the full
head-coherent condition, not a monochromatic-edge substitute. QED.

For equal radices `q>=3`, the universal bound `h+2` is sharp. Begin with
three words with common prefix of length `h-1` and final digits `0,1,2`,
oriented as a directed triangle. Successively add a word whose first
nonzero digit is one position earlier than all preceding nonzero digits,
and orient all preceding vertices toward it. The initial three vertices
each have one incoming edge; each added vertex receives edges whose
first-difference position and source digit agree. This constructs a
coherent `h+2`-vertex tournament. It does not assert that this tournament
is induced by the cyclic regular orientation used next.

## The exact family-132 contract

**Theorem 2.** For every integer `q>=3`, set

\[
 M=[13(q-1)]^2,\qquad r=\lceil\sqrt M\rceil=13(q-1),
 \qquad k=2M^2+1.
\]

There is a uniform deterministic labelled regular tournament on
`{0,...,k-1}` having exactly the required label alphabet `{0,...,r-1}`,
outdegree `M^2` at every vertex, and no head-coherent set of 16 vertices.
Orientation and one label can each be evaluated with `O(log M)` bits of
storage and conservatively `O((log M)^2)` elementary bit operations.

### Construction and proof

Represent `i` in base `q` as a word of exactly 13 digits, with leading
zeros. Direct

\[
 i\longrightarrow j
 \quad\Longleftrightarrow\quad
 1\le (j-i)\bmod k\le M^2.
\]

Every vertex has precisely `M^2` successors, and the odd value of `k`
ensures exactly one direction for each pair. Use (1) with 13 equal
radices on its directed edges. The label alphabet has size `13(q-1)=r`.

There are enough words. For `q=3`, the inequality is the exact calculation

\[
 k=913953<1594323=3^{13}.
\]

For `q>=4`,

\[
 q^{13}-k
 =q^{13}-2\cdot13^4(q-1)^4-1
 >q^4(q^9-2\cdot13^4)-1>0,
\]

because `4^9=262144 > 2*13^4=57122` and all quantities are integers.
Theorem 1 bounds every coherent set by `13+2=15`. This excludes exactly
the forbidden 16-vertex condition.

The generator receives `q`, or recovers it from an admissible `M` by
integer square root and `q=1+sqrt(M)/13`. All inputs and every intermediate
integer have `O(log M)` bits. Computing the fixed 13 digits, the first
difference, a palette offset, and a modular difference uses a constant
number of ordinary integer operations. Schoolbook arithmetic gives the
stated conservative bit bound. There is no preprocessing depending on
`k`, and evaluating an edge does not instantiate the tournament.

The infinite parameter family is unbounded. In particular, for any
recursive depth `d`, its members eventually satisfy the published
quantitative restriction `M>=9^(d+1)`. The constant word length 13 is
independent of that recursive depth.

The executable implementation is `checks/label_contract.py`, class
`SuccinctTournament`, and uses this compressed label formula. For example,
`--q 3 --edge 0 1` evaluates one edge of the 913953-vertex tournament while
holding only a few integers.

## Optional finite-parameter refinements

These are direct applications of Theorem 1, not a claim of globally
optimal parameters or a new sensitivity estimate.

* Thirteen digits, with three radix-two positions and ten radix-three
  positions, have `R=23` and capacity `2^3*3^10=472392`. They admit
  `M=485`, since `ceil(sqrt(485))=23` and `2*485^2+1=470451`.
* Fourteen digits, with six radix-two positions and eight radix-three
  positions, the **last position radix two**, have `R=22` and capacity
  `2^6*3^8=419904`. They admit `M=442`, since
  `ceil(sqrt(442))=22` and `2*442^2+1=390729`. The last-radix refinement
  bounds coherent sets by `14+1=15`.

The checker supports arbitrary radix lists for local contract diagnostics;
its public `SuccinctTournament` interface deliberately uses the simple
uniform family of Theorem 2. Integration may choose a smaller finite
seed without changing the infinite-family proof.

## Verification, scope, and the next obstacle

The checker independently reconstructs the fixed-head labels by listing
the digits other than the head digit. It exhausts every orientation of
every five-vertex subset of the two-digit ternary cube, where a coherent
five-set would violate Theorem 1, and every orientation of the binary
two-digit cube. These are nonvacuous small analogues, not an exhaustive
check of a large tournament. It also checks a sharp coherent 15-vertex
example, exact parameter inequalities, cyclic-orientation arithmetic,
and representative large-index labels. The proof above, not those finite
diagnostics, establishes the infinite-family theorem.

Run from the topic directory:

```sh
python3 checks/label_contract.py --self-test
```

The check was run once on 15 October 2026 under a 30-second subprocess
timeout. It passed all 129088 enumerated small tournaments and the other
listed diagnostics in 1.826 seconds, using one serial Python process and
materializing zero large tournaments. An independent agent then reviewed
the saved proof and code without finding a defect or repeating the tests.

The elementary first-difference mechanism is proved, so it is not being
retired as an unsuccessful heuristic. The remaining research obligation
is historical scope: distinguish this exact directed coherence bound and
its family-132 application from known first-difference/canonical Ramsey
colourings. The construction makes the labels succinct; it does **not**
claim a stronger sensitivity exponent than the published profile
recurrences, or logarithmic-time evaluation of the full recursively
defined Boolean function. Those are separate questions.
