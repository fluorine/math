# Snaky within nineteen Maker moves

15 October 2026

## Abstract

We give a finite, independently checked certificate that Maker can force
Snaky within nineteen of Maker's own moves on the initially empty infinite
square board. The same certificate proves the bound on a 17×17 board. It
combines Nándor Sieben's twenty-move strategy with local tactics from Trevor
Morris's 15×15 certificate. The construction retains all acquired Maker
stones and tracks a larger region known to contain no Breaker stone, allowing
previously discarded safe cells to be used again. The resulting 3,468-card
certificate uses the existing declarative rules. Its soundness follows by
induction on card height, with a universal response class for moves outside
the support. We make no optimality claim.

## 1. Game and theorem

The board is either `Z²` or `Q = {0,…,16}²`. Maker moves first. On each turn
the player claims exactly one previously unclaimed cell. Breaker only blocks;
Breaker completing a shape does not end the game. Maker wins upon owning a
translated, rotated, or reflected copy of

\[
F=\{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)\}.
\]

Other Maker stones are allowed: the six-cell condition specifies a winning
subset. A move bound counts actual Maker claims, including the winning claim,
and does not count alternating plies.

**Theorem.** From the empty board, Maker has a strategy that completes a copy
of `F` by Maker's nineteenth move against every legal Breaker strategy. This
holds both on `Z²` and on `Q`.

The data establishing the theorem are
[`certificate/snaky19.cards.txt`](certificate/snaky19.cards.txt), with SHA-256

```text
baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e
```

The file contains 3,468 cards, all reachable from root 3467. The root has
height 19, no required Maker stones, first move `(8,8)`, and a 249-cell support
contained in `Q`. Its longest dependency route also has height 19.

## 2. Declarative certificate and soundness

A card is a tuple `C=(A,S,p,h)`: finite integer-cell sets `A` and `S`, a pivot
`p∈S`, and a positive integer height `h`. Its intended meaning is that Maker
can win within `h` further claims whenever Maker owns `A` and Breaker owns
no cell of `S`. Extra Maker stones are permitted. Cards can be placed by any
map `g(x)=Dx+t`, where `D` is one of the eight symmetries of the square and
`t∈Z²`.

A card is terminal if `A∪{p}` contains a copy of `F`. Otherwise it must provide
the following hints. Each hint selects another card `(A',S',p',h')` and a map
`g`, with

\[
h'<h,\qquad g(A')\subseteq A\cup\{p\}.
\]

For every `w∈S\(A∪{p})`, an inside-response hint must additionally satisfy
`g(S')⊆S\{w}`. An outside-response hint must satisfy `g(S')⊆S`. The latter
is one universally valid rule, not an assumption that Breaker can pass.
It applies to every legal claim outside `S`, including holes in its bounding
rectangle and points arbitrarily far away.

The finite checker verifies these inclusions, all required response classes,
the coordinate maps, terminal geometry, and strict height decreases. The
construction algorithm is not part of the certificate's logical premises.

**Soundness lemma.** Let every card satisfy the preceding rules. At a Maker
turn on `Z²`, let `M,W` be the finite, disjoint ownership sets. If an instance
of a height-`h` card satisfies `g(A)⊆M` and `g(S)∩W=∅`, Maker can complete
Snaky within at most `h` additional claims.

**Proof.** Induct strongly on `h`. A position already containing Snaky is
already won. Otherwise, if `g(p)` is unowned, Maker claims it; the claim is
legal because `p∈S` and the support is Breaker-free. If `g(p)` is already
Maker's, Maker instead claims any fresh cell. Such a cell exists because the
histories are finite and the board is infinite. This is an actual claim and
is charged to the height budget. In either case the resulting Maker set
contains `g(A∪{p})`.

If the terminal condition holds, Maker now owns the required six-cell copy.
Otherwise consider an arbitrary legal Breaker claim `w`. If `w∈g(S)`, its
unique preimage is outside `A∪{p}`, since Breaker cannot claim Maker's stones.
The corresponding checked hint gives a child whose required stones are owned
and whose support avoids both the old Breaker stones and `w`. If `w∉g(S)`,
the outside hint supplies the same conclusion. Composition of square
symmetries and translations preserves the allowed maps and winning shapes.
The child has height at most `h−1`; induction therefore bounds the total by
one Maker claim plus `h−1`. These two reply cases exhaust `Z²`. ∎

For the finite board, the same proof uses the capacity invariant

\[
|M|+|W|+2h\leq |Q|.
\]

It supplies a free cell for an already-owned pivot's replacement claim and
for a nonterminal Breaker reply. After one claim by each player and a strict
height decrease, the invariant persists. Root support containment keeps all
subsequent supports on the board; child requirements are contained in already
owned stones. At the empty root, `2·19≤289`. Applying the lemma directly on
the plane, and its finite version on `Q`, proves both assertions. The
infinite-board conclusion does not rely on pretending that outside-board
Breaker moves are legal passes in a finite game.

## 3. Construction by retaining history and safe space

The starting twenty-move certificate has 1,738 cards. Reconstructing its
dependency graph gives 15,696 maximum-height labelled routes through 59
critical cards. Full-history replay distinguishes 9,792 routes that repeat
a planned Maker stone, 2,592 with an already-occupied Breaker reply, 864 with
an earlier global win, and 2,448 genuine twenty-move routes. Thus simply
correcting this bookkeeping does not establish nineteen moves.

Fix the initial baseline support `U`. During construction retain the full
Maker set `M` and the actual Breaker set within `U`, giving the safe region
`E=U\W`. A local template may forget stones and reduce its support, but these
known facts about the actual position remain available.

For a remaining budget `b`, the constructor tries a transformed catalog card
with height at most `b`, requirements contained in `M`, and support contained
in `E`. If one fits, its certified strategy closes that node. Otherwise the
constructor follows the baseline move. Replies whose existing hints already
fit the smaller budget retain those hints; the other replies are processed
recursively. Every claim inside `U` remains a separate possible update of
`W`, even when outside the current template. Only claims outside `U` are
merged, since every future support remains inside `U`.

Using only the twenty-move catalog left an unresolved branch. Adding the
8,671-card catalog underlying Morris's 15×15 result closed the whole root.
That catalog's root has height 25; its usefulness here lies in its local
tactics, not in a better standalone move bound.

The successful construction uses 180 catalog substitutions. All 180 reclaim
safe cells outside the current baseline support; 68 also use Maker stones
forgotten by the baseline requirements. Seventeen distinct 15×15 tactics
account for 164 substitutions, and three twenty-move tactics account for
the remaining 16. No zero-cost repeated-pivot shortcut is used in this run.

Three early substitutions illustrate how the surviving long branches are
removed. IDs below are zero-based IDs in the public 15×15 catalog. Coordinates
are in the final root frame, immediately before Maker's next claim.

* With `M={(8,8),(8,9)}` and `W={(7,8),(9,9)}`, replace baseline card 1702
  of height 18 by source card 28 of height 17 under
  `g(x,y)=(y+2,x+3)`. Its next move is `(8,10)`. Two Maker claims have
  already occurred, so this continuation has total bound 19.
* With `M={(8,8),(8,9),(11,8)}` and
  `W={(7,8),(8,10),(12,8)}`, replace baseline card 1036 of height 17 by
  source card 79 of height 15 under `g(x,y)=(14−x,y+3)`. Its next move is
  `(11,9)`, giving total bound 18 on this branch.
* For the same `M` and `W={(7,8),(8,10),(13,8)}`, use source card 145 of
  height 14 under `g(x,y)=(y+4,12−x)`. Its next move is `(9,8)`, giving total
  bound 17 on this branch.

These examples do not replace verification of the remaining replies.
The constructor exports every new decision as an ordinary card, initially
with requirements `M` and support `E`. It then discards support cells unused
by its pivot, requirements, and child supports. Reachability pruning and
reindexing leave 1,662 twenty-move-source cards, 1,653 15×15-source cards, and
153 newly composed cards. Exact source IDs and transformation witnesses are
recorded in [`constructor/`](constructor/README.md).

## 4. Computational evidence and reproducibility

The independent Python verifier shares no constructor checking helpers. For
the exact delivered file it checked 61,040 inside-response obligations,
3,456 universal outside-response obligations, and twelve terminal cards.
It accepted empty root requirements, support containment, and height 19.

The verifier's tests include malformed terminal shapes, missing inside or
outside replies, invalid transforms, broken ownership/support inclusions,
invalid references, and incorrect height descent. Controls applied to the
final file rejected both lowering the root height to 18 and deleting its
reply at `(0,4)`. The first rejection concerns this certificate's declared
dependencies; it does not prove that an eighteen-move strategy is impossible.

The deterministic construction used Python 3.9.6, one computational thread,
no random seed, a 120-second wall limit, and a two-million-call cap. The
successful run took about fifteen seconds. The certificate can be checked
offline using only the Python standard library:

```sh
python3 topics/snaky/reproduce.py
```

Adding `--reconstruct` regenerates the certificate from the pinned source
files and requires byte-for-byte identity.

The completed argument here is the independently checked data together with
the soundness proof above. The direct plane soundness development
`formal/Snaky/Plane.lean`, including `Snaky.cards_sound_plane_in`, has compiled.
`formal/Snaky/Result19.lean` states `Snaky.snaky_wins_17x17_in_19` and
`Snaky.snaky_wins_plane_in_19`. The full generated `Gen19` kernel check is
still in progress at this manuscript revision; a completed kernel build is
not yet claimed. The Python implementation and runtime remain part of the
completed computational check's trust assumptions.

## 5. Attribution, novelty, and scope

The twenty-move strategy is due to [Nándor Sieben](https://github.com/nandorsieben/Snaky/tree/a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa),
building on [OpenAI's twenty-one-move strategy](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a).
[Trevor Morris's repository](https://github.com/gotrevor/snaky-15x15/tree/b18ed32473a6a22ebfdda98da62d61b8b1590c1e)
supplies the compact card interface, its soundness development, the converted
twenty-move certificate, and the 15×15 tactic catalog. We reuse and credit
those tactics; the contribution here is their history-aware composition
into a uniform nineteen-move certificate. Pinned revisions, hashes, and the
retained upstream license are documented in `reference/README.md`.

The [15 October 2026 novelty audit](NOVELTY.md) inspected these primary
sources, the public bounds tracker, and searches for nineteen-move-or-better
strategies. It located twenty moves as the strongest public bound and found
no matching nineteen-move result. This is a bounded audit, not proof that
no unindexed or unpublished result exists. We establish an upper bound and
claim neither optimality nor any global Breaker lower bound.
