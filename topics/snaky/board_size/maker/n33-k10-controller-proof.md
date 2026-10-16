# N33 K10 controller: independently checked conditional defense

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py n33_k10_controller --output /tmp/n33_k10_controller-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


Status: the single approved finite audit passed on 16 October 2026. It proves
a complete conditional physical Breaker defense at the exact N33 position.
The accepted L_cap K8 source and report remain unchanged. The
[audit report](../verification/n33_k10_controller.json) and
[execution receipt](../verification/n33_k10_controller.execution.json) preserve
the complete data and source bindings.

The exact physical Maker-turn state has 33 Maker and 33 Breaker stones on
the 14×14 board. Its full colors are pinned both in the
[submitted prompt](../browser/02-twentyfirst-prompt.txt) and in the `parent`
of the accepted [sixteenth-response report](../verification/browser_sixteenth_maker02.json).
The new checker also derives those colors from the previously bound T_cross
state, removing only the four explicitly recorded moves of each color.

The reserved cells are a=(11,8), b=(13,8), c=(13,9), d=(12,9), e=(14,7),
g=(14,8), h=(14,9), i=(14,10), j=(12,7), k=(12,8). The exterior matching Q
is the accepted L_row 54-pair certificate after deleting {b,e}, {c,h},
and {g,i}. It has 51 pairs disjoint from all ten reserved cells. The checker
verified that their 102 endpoints, the reserved ten, and the declared
18 unmatched exterior cells partition all 130 initially free cells.

The controller has two waiting phases. Initially, Maker's first
reserved entry other than k receives actual Bk and the specified Table I
pairing commitment. Mk receives actual Bj and enters the exact accepted
L_cap state, with the remaining K8 pristine. That second phase uses the
accepted Table II. In either waiting phase, an exterior Maker claim receives
its free Q-mate if one is required. Otherwise Breaker makes the phase's
specified reserved commitment, Bk or Bd. There is no unrestricted filler
while a pristine domain is needed. After commitment, Breaker takes a free
selected-pair mate when required and otherwise the lexicographically least
free physical cell, ordered by x then y. If the board is exhausted, no reply
is invented.

The [new finite checker](../verification/n33_k10_controller.py) regenerates
all 1,040 literal Snakies independently of the proposal. It requires exactly
the ten displayed live targets with no Q pair, preserving their complete
physical coordinates. The free exterior cells (14,11) in W5 and (12,11) in
W8 are retained; preventing their reserved traces suffices regardless of
those exterior colors. Every other live target has an actual protecting
Q pair. Old blocked targets stay blocked.

At each Maker-turn boundary while waiting, every Q pair is either untouched
or already has a Breaker endpoint. A fresh Maker claim cannot complete a Q
pair before the mate response. Waiting replies touch no reserved cell except
the explicit transition or commitment. Each of the ten no-Q traces requires
at least three pristine cells in phase I. After Mk/Bj, the two j-targets are
blocked and every remaining trace requires at least two pristine K8 cells.
Thus an exterior move or the first local entry cannot complete a target
before the specified response. The checker tests these requirements and
all 130 initial physical entries, plus the 128 entries at the exact phase-II
boundary.

Each of the 19 commitments must either hit every no-Q trace with the actual
Breaker response or leave a fresh internal pair contained in it. Previously
touched Q pairs are already physically blocked; untouched Q pairs remain
free. No earlier exterior Maker or Breaker stone is discarded. The checked
two-endpoint invariant handles every exterior interleaving and arbitrary
extra Breaker insertions after commitment. A Maker-owned mate cannot coexist
with a legal fresh claim of its other endpoint at a turn boundary. Every
immediate Maker claim, including the final legal one, therefore remains safe.

For an additional finite check, each committed local residual is replayed
against every fresh relevant Maker entry, an outside class, and every possible
local filler when no mate is required. Actual blocked targets are removed,
and actual Maker-owned core cells are removed only from remaining requirements.
An empty requirement is rejected as an immediate win. The active domains have
at most seven cells; omitted irrelevant core cells are included in the outside
class. This is an overapproximation of the specified physical filler rule,
not a physical pass. Real play terminates because each turn claims a fresh
physical cell.

The audit checked all 270 live targets among the 1,040 literal placements:
260 have an exterior Q pair and ten require the reserved controller. Its
19 commitment replays checked 7,884 states, 24,840 Maker entries including
outside, 54,468 arbitrary filler transitions, and 1,857 final local Maker
claims. All 16 negative controls passed. The waiting and committed pair
invariants and a separate final-claim fixture also passed.

The run used 0.169650 CPU seconds and 0.421858 guarded wall seconds, with
28,229,632 bytes peak RSS, exit code 0, and no guard events. The fixed limits
were 8 internal CPU / 25 internal wall seconds under the unchanged
10 CPU / 30 wall / 100 MiB guard. Source SHA256 is
`578824d775a25e8e82e65b50f28efc4a0e0213ae46f140ad9a9e0561d20458cb`;
report SHA256 is
`a313b81fbb08c72e3ffe7c17552dc336ace699eafa50bf77146c6b0b511fa61f`.
No second run or source change was needed. This result does not prove an
earlier-state loss or any empty-board outcome.
