# Soundness of the baseline certificate rules

This argument separates finite data checking from game semantics. It proves
the meaning of any accepted card set. The independent verifier has accepted
`certificate/snaky19.cards.txt` with empty root requirements and root height 19;
applying the argument to that file establishes the stated infinite-board bound.
The earlier public reference set has root height 20.

Fix a finite collection of valid cards as specified in `SPECIFICATION.md`.
We prove by strong induction on h: at any Maker turn on Z² with disjoint finite
sets M,B, if a transformed card of height h satisfies `g(A)⊆M` and
`g(S)∩B=∅`, Maker can force completion within at most h additional claims.
A position already containing Snaky is already won and needs zero claims.
Square symmetries and translations preserve the family of Snaky placements.

If `g(p)∉M`, claim g(p). This is legal because p∈S and g(S) avoids B.
The resulting M contains `g(A∪{p})`. If the terminal rule holds, Maker now
owns a Snaky. Otherwise consider an arbitrary legal Breaker move w. If
`w∈g(S)`, its unique preimage is not in `A∪{p}`, since Breaker cannot claim
Maker's stones. The checked reply hint gives a lower-height card whose Maker
prerequisites are now owned and whose support avoids both the old B and w.
If `w∉g(S)`, the pass hint does the same. Thus the induction hypothesis wins
within at most h−1 further claims after the one just spent. These two cases
cover every integer cell, including cells outside any displayed envelope.

If `g(p)∈M`, there are two sound implementations. The baseline proof may
claim any free cell and then apply exactly the preceding argument; infinity
guarantees a free cell and the extra Maker stone cannot invalidate any
prerequisite. A sharper implementation, when the card is nonterminal, invokes
its pass hint immediately: that child's requirements already hold before
any player moves, and its height is strictly smaller. If the card is terminal,
M already contains a Snaky. This sharper step is a logical change of the
certificate being consulted, not a game move. Strictly decreasing height
prevents an infinite sequence of such deductions.

Starting from the root with empty M,B, the root A is empty, all of S is safe,
and the induction gives a legal policy against every Breaker strategy. The
height bounds **actual Maker claims**, including the last claim, and extra
Breaker stones outside support do not matter. This proves the infinite-board
interpretation directly, without assuming that a finite-board player can
pass or overlooking outside-board replies.

For the finite-board reference theorem, all used images of A and S lie on
the board and `|M|+|B|+2h≤N` ensures a free cell whenever a dummy claim or
Breaker response is needed. After one move by each player and a decrease in
height, the inequality persists. At the empty root this follows from
`2h≤N`. This is the capacity invariant in the upstream Lean proof.

## Retained-history invocation

More generally let U be a fixed finite subset of Z², M the full known Maker
set, and E a subset of U proved to avoid all Breaker stones. Any accepted card
under a square symmetry/translation with `g(A)⊆M` and `g(S)⊆E` may be invoked.
The preceding induction establishes its bound, regardless of the construction
method that found it. When Breaker moves within U, remove that cell from E;
when outside U, E stays unchanged. All future card supports must remain in U.
This justifies using more history and more safe space than the current card
retains, but **only** when the full response partition preserves those facts.

## Verification obligations

An implementation must check the data premises: exact target shape, each
terminal, each required response, strict height decrease, set inclusions and
all coordinate maps. Independent rejection controls must exercise malformed
terminals, missing responses, illegal maps, invalid prerequisites, and incorrect
heights. A successful source-code or parser run is not a proof unless these
premises hold for the exact delivered certificate. No finite search failure
establishes a lower bound against all infinite-board Maker strategies.
