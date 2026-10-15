# Game and declarative certificate specification

## Game

Cells are integer pairs `(x,y)` in Z². Positions are disjoint finite sets `M`
(Maker) and `B` (Breaker). Initially both are empty and Maker moves first.
Each player claims one cell outside `M∪B`, alternating. Maker wins immediately
when `M` contains a translate of a D4 image of
`Q={(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`. The objective counts Maker claims,
including the claim completing Q, rather than individual player turns.
Breaker need not make any shape. Extra Maker stones never invalidate a win.

## Reference card system

A card is `(A,S,p,h,pass,replies)`. A and S are finite sets of integer pairs;
p is a pair, h a positive integer. Its meaning at a Maker turn is:
if `A⊆M` and `S∩B=∅`, Maker can force a win within h further Maker claims.
S is Breaker-free, **not necessarily empty**; A need not be contained in S.
All images of cards may be translated and transformed by a square symmetry.

A hint `(j,k,dx,dy)` references card j under symmetry k and translation (dx,dy).
The ordered matrices for k=0,…,7, written `(a,b,c,d)` for
`(x,y)↦(a*x+b*y+tx,c*x+d*y+ty)` with translation `(tx,ty)`, are:

```
(1,0,0,1), (-1,0,0,1), (0,-1,1,0), (0,1,1,0),
(-1,0,0,-1), (1,0,0,-1), (0,1,-1,0), (0,-1,-1,0)
```

Arbitrary integer matrices are not symmetries.

A valid card has `h≥1` and `p∈S`. It satisfies either the terminal rule or all
continuation rules:

1. **Terminal:** `A∪{p}` contains a translate of a D4 image of Q.
2. **Outside reply:** pass cites a card of height `<h` whose transformed A lies
   in `A∪{p}` and whose transformed S lies in S.
3. **Each inside reply:** for every `w∈S\(A∪{p})`, a reply hint cites a card of
   height `<h` whose transformed A lies in `A∪{p}` and whose transformed S lies
   in `S\{w}`.

All referenced cards must themselves be valid. A root has A empty. For the
finite-board reference claim its S fits inside the declared rectangular board
under its root transform, and `2h≤rows*cols`. This finite capacity condition
is not needed for Z². On the infinite board the outside class is always a
genuine possible response class. It is not a rule allowing Breaker to pass.

## Compact reference encoding

The UTF-8 first line is
`snaky-cards-txt-v1 rows cols root symmetry translation_x translation_y`.
Subsequent lines define cards with implicit zero-based consecutive IDs:

```
h px py |A| Ax Ay ... |S| Sx Sy ... pass |replies| reply ...
```

Here pass is `-1` (absent) or four integers `j k dx dy`. Each reply is six
integers `wx wy j k dx dy`. A strict parser rejects truncation, extra tokens,
invalid indices, duplicate coordinate entries/response keys and invalid
symmetry codes. The independent checker must not silently normalize malformed
syntax into a different valid theorem. Terminal cards may omit continuations.

## Research extensions and acceptance boundary

These are sound candidate construction tools; their description does not claim
that they achieve 19 moves.

- Keep all accumulated M instead of only a template's A. When a nonterminal
  card's p already belongs to M, its pass child is applicable immediately. This
  is a zero-cost logical deduction, not a Maker pass or a new Breaker turn.
- Retain guaranteed safe cells E inside a fixed finite universe U. An arbitrary
  transformed validated card may be invoked when `A⊆M` and `S⊆E`.
- Initially `E=U`. Every observed Breaker move w inside U removes w from E,
  even when outside the currently selected card's support. Moves outside U
  form one class only while every future support remains inside U.

It is unsound to merge a Breaker move inside U into a generic outside-current-
support class and subsequently use its unrecorded cell as safe. Explicit
branching, a conservative safe-set representation, or a proved equivalence
must justify each merged class. A final certificate must give all responses,
exact coordinate maps, legal Maker claims and an upper bound on every branch;
search results alone are not accepted proofs.
