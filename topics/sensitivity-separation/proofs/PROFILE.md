# Coupled candidate bounds for the actual nested predicates

Status: proved below for the construction and profile definitions in the pinned
family-132 source. This is a structural refinement of its four-profile
recurrence, not a claim of a new tournament architecture or a literature-wide
priority claim. Numerical propagation and construction costs are handled in the
integration report. The finite checker is a regression check, not the proof.

## Statement

Write the preceding level's actual profiles as

\[
 A=S'_0,\qquad B=S'_1,\qquad C=J'_0,\qquad D=J'_1.
\]

They satisfy `0 <= C <= A` and `0 <= D <= B`. With the same labelled
tournament forbidding a head-coherent set of 16 vertices, the next profiles obey

\[
\begin{aligned}
 S_0&\leq\max\{A+14C,\ A+13C+B,\ 15C+D,\
                       13C+B+D,\ 14C+2D,\ 12C+3D\},\\
 J_0&\leq\max\{A+14C,\ A+13C+D,\ 15C+D,\
                       14C+2D,\ 12C+3D\},\\
 S_1&\leq M^2 A+rB,\\
 J_1&\leq M^2 C+rB.
\end{aligned}
\tag{1}
\]

As in the source, the joint profiles at the final level are zero by the
empty-maximum convention. All expressions in (1) have nonnegative
coefficients, so componentwise upper bounds can be propagated through this
maximum without assuming those comparison bounds themselves satisfy `C <= A`
or `D <= B`.

The change to the zero side uses two facts absent from the displayed source
recurrence: most candidate targets require a joint child flip, and the target
and gate candidate counts cannot attain their independent maxima together.
It is not obtained merely by iterating the published inequalities or replacing
their coefficient 16 by 15. For example, at `C=D=0`, (1) gives
`S0 <= A+B` and `J0 <= A`, whereas the published bounds give `16A+B`
and `16A`. This compares the certified bounds; it does not assert either is
the exact sensitivity of every instance.

## Local setup and head coherence

At a fixed parent index, write `Q` for the strongest child index and `g<Q`
for its gate index. Clause `i` requires `P_Q=1` in every child of row `i`
and `P_g=0` in child `(j,a(i,j))` for every edge `i -> j`.
Each condition of one clause uses a distinct child.

Fix a zero input. Let `T` be the clauses with exactly one failed target and
no failed gate, and let `G` be the clauses with exactly one failed gate and
no failed target. Every successful single-coordinate flip repairs a member of
these lists. The lists are fixed before the coordinate is chosen. Write `m_t`
for the unique failed-target position of `t in T`.

A vertex set is **head coherent** when, at every head, all incoming edges
inside the set have the same label. A head with no incoming edge imposes no
condition. This is exactly the source's labelling contract. It is not a
condition on labels leaving a vertex.

For an edge `s -> t` inside `T`, the passing gate in row `t` implies
`P_g=0`, hence `P_Q=0`, at its labelled child. Since the row has only one
failed target, `a(s,t)=m_t`. Thus `T` is head coherent and `|T|<=15`.

There is no edge from `T` to `G`: every child in a `G` row has `P_Q=1`
and therefore `P_g=1`, which would fail a gate of the `T` clause.
Consequently every `G` vertex points to every `T` vertex.

Every outgoing edge within `G` is a failed gate. Each `G` vertex has at
most one such edge, so counting the edges of its induced tournament gives
`|G|(|G|-1)/2 <= |G|`, and hence `|G|<=3`. If `|G|=3`, it is a directed
3-cycle, and each vertex's unique failed gate is internal. If `|G|=2`,
the tail of the internal edge also has its unique failure internal.

## Which repairs are joint

Call a target in `T` **ordinary** when `P_g=1` at its unique failed target;
otherwise call it **joint**. Repairing a joint target changes both `P_g`
and `P_Q` from zero to one, so its repair coordinates number at most `C`.
An ordinary target costs at most `A`.

An ordinary target has no incoming edge from `T`, because such an edge
would require `P_g=0` at its missing target. A tournament has at most one
vertex with indegree zero, so there is at most one ordinary target.
Moreover, an ordinary target's entire row has `P_g=1`. Every `G` vertex
therefore uses its unique failed gate on that row. If `|G|>=2`, the
internal edge of `G` already consumes one failure, a contradiction.
Thus `|G|>=2` forces **all targets to be joint**.

Call a gate candidate **ordinary** when its failed gate child has `P_Q=0`,
and **joint** otherwise. A joint gate starts with `P_g=P_Q=1`; repairing
it sets both to zero, so it costs at most `D`. An ordinary gate costs at
most `B`. Every gate failure internal to `G` is joint. Hence at most one
gate candidate can be ordinary, and no gate candidate is ordinary when
`|G|=3`.

## The coupled counting table

Passing edges from `G` into `T` have label `m_t` at their head. Internal
edges of `G` are head coherent when `|G|<=3`: in the three-vertex case
each head has just one incoming edge, and the smaller cases are immediate.
There are no edges from `T` into `G`.

| Gate candidates | Extra condition | Target bound and repair cost | Gate cost |
|---|---|---|---|
| 0 | — | at most 15, at most one ordinary: `A+14C` | 0 |
| 1 | an ordinary target or an ordinary gate exists | at most 14, at most one ordinary: `A+13C` | at most `B` |
| 1 | neither exists | at most 15, all joint: `15C` | `D` |
| 2 | the sink's failed gate is ordinary | at most 13, all joint: `13C` | `B+D` |
| 2 | both failed gates are joint | at most 14, all joint: `14C` | `2D` |
| 3 | directed 3-cycle | at most 12, all joint: `12C` | `3D` |

Here are the details establishing every improvement in the table.

* **One gate candidate, with an ordinary gate.** If its failed gate points
  into `T`, its child must be the row's unique failed target: all other
  children have `P_Q=1`. Its label is therefore `m_t` even though the gate
  fails. All labels within `T union G` agree at each head, so that union
  is head coherent and has size at most 15. The same conclusion holds if
  the failed gate points outside `T`.
* **One gate candidate, with an ordinary target.** Its failed gate must
  point into that ordinary target's row. That target is a source of the
  tournament on `T`. It has only one incoming edge in `T union G`, namely
  the edge from `G`. Choose its head label to be the label of that edge;
  there is no competing incoming label. Every other head keeps its
  existing coherent label. Thus `T union G` is head coherent even if
  this one edge's label differs from the missing-target position. Again
  `|T|<=14`. This reassignment is essential.
* **One gate candidate, neither ordinary type present.** Use `|T|<=15`;
  every target and the gate have joint repair cost.
* **Two gate candidates, with an ordinary sink gate.** The other gate
  failure is the internal edge. If the sink's failed gate points into
  `T`, its label is again `m_t`, since its child has `P_Q=0`. Thus all
  head labels in `T union G` agree, giving `|T|+2<=15`. In fact an
  ordinary failed gate into `T` cannot occur here: that target's whole
  row would have `P_g=1`, contradicting the passing gate from the other
  `G` vertex. Either argument gives the stated bound.
* **Two gate candidates, both joint.** Only the sink can have a failure
  outside `G`. All `G -> T` labels match `m_t` except possibly at the
  head of that one failure. Remove that target, if it exists. The
  remaining union is head coherent, giving `|T|-1+2<=15` and hence
  `|T|<=14`. All targets are joint.
* **Three gate candidates.** All failed gates are internal, so all gates
  into `T` pass. The full union is head coherent. Thus `|T|+3<=15`.

Taking the maximum of the six rows proves the ordinary zero inequality
in (1). Union bounds over repair coordinates are legitimate even when
several candidate clauses use the same child.

## Joint zero transitions

Fix two parent indices `q<q'` and an input where both parent predicates
are zero. Their child gate indices satisfy `g'=Q-q' < g=Q-q < Q`.
Form `T` using the **stronger** index `q'`. Form `G` using the stronger
index as well, but retain only gate candidates whose unique failed gate
is also failed at the weaker index `q`.

Every flip taking both parent predicates to one satisfies some clause
at `q'`. Initially that clause has exactly one failed condition at
`q'`, since one coordinate affects only one condition of the clause.
If that failure is a target, it belongs to `T`. If it is a gate, all
other gates already pass at `q'` and hence at `q`; the assumption that
the weaker parent is initially zero forces this same gate to fail at
`q`. It therefore belongs to the retained `G`. These fixed lists
cover all joint-success coordinates, even though the successful witness
can depend on the coordinate.

The entire preceding combinatorial argument applies to these lists,
with gate index `g'`: deleting some gate candidates does not affect any
of its premises. Ordinary target repairs cost `A` and joint target
repairs cost `C`. Every retained gate, including an ordinary one, now
costs at most `D`, because its two distinct predicates `P_g,P_g'`
start at one and must both become zero to satisfy the stronger clause.
Substitute `B=D` in the counting table. Its fourth row `13C+2D`
is dominated by its fifth row `14C+2D`. The remaining five rows give
the joint zero inequality in (1).

For one-to-zero transitions, choose a clause initially satisfied at the
relevant index, or at the stronger of the two indices. The source's
fixed-clause argument gives the unchanged one-side inequalities in (1).
This completes the proof for every input and index; taking maxima gives
the stated profiles.

## Exact obstructions and scope of sharpness

The checker stores explicit local models using two child positions and
states `0=(P_g,P_Q)=(0,0)`, `1=(1,0)`, `2=(1,1)`. They show why the
following stronger shortcuts are false.

* **Not every target repair is joint.** A source of `T` can have state
  1 at its missing target. The first table row permits one ordinary
  target for this reason.
* **`T union G` need not be head coherent, and `|T|+|G|<=15` is false.**
  Take 15 target vertices in a transitive tournament, each with row
  `(0,2)`, and one gate vertex with row `(2,2)` dominating them.
  Label all internal edges 0 except the gate vertex's edge into the
  last target, labelled 1. Every target is a candidate and the gate
  vertex has one failed gate. The full 16-set is incoherent at the
  last target, whereas the 15 targets are coherent. Thus it obeys
  the no-coherent-16 contract on this local tournament and has 16
  candidate vertices. A two-gate version has 14 targets and 2 gates.
* **`|G|<=2` is false.** Three full-target rows on a directed 3-cycle
  have exactly one failed internal gate apiece. Their three repair
  children are distinct. A model with identical nested child
  predicates on a single bit has three different repairing flips,
  so the coefficient 3 cannot be removed merely by counting gate
  candidates. Such a cycle of gate candidates can also be placed
  inside a larger regular tournament, with other rows having all
  predicates zero.
* **Source labels cannot replace head labels.** On the transitive
  triple `0 -> 1`, `0 -> 2`, `1 -> 2`, labels `(0,0,1)` are constant
  at each tail but conflict at head 2. Conversely `(0,1,1)` are
  head coherent and conflict at tail 0.

There are also explicit templates attaining each row's candidate counts
and ordinary/joint types. This is sharpness of the **local counting
argument**, not a claim that all four global sensitivity maxima can be
attained together by one input of the recursive family, nor a proof of
an optimal exponent. The local 15/16-vertex templates are not themselves
the required full regular labelled tournament. No extension theorem or
global family optimality is inferred from them.

## Reproduction

Run `python3 topics/sensitivity-separation/checks/profile_local.py`.
It exhausts all three-vertex tournaments, all two-label edge assignments,
and all nested two-threshold row states with two children per row;
checks the structural assertions and weighted envelopes; verifies the
six exact counting templates; and checks the head/tail counterexamples.
It does not search for a tournament satisfying the main explicitness
target or substitute finite computation for the proof above.

Source definitions and original recurrence:
[construction](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/01-construction.tex),
[recurrences](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/build/sections/02-recurrences.tex).
