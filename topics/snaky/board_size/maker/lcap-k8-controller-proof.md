The eight-cell controller passed its independent finite check on 16 October

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py lcap_k8_controller --output /tmp/lcap_k8_controller-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).

2026. It is a complete ordinary physical Breaker defense at the exact saved
`L_cap` position, with 34 Maker and 34 Breaker stones on the 14×14 board.
The [verifier](../verification/lcap_k8_controller.py) and
[complete report](../verification/lcap_k8_controller.json) preserve the full
old colors and every protecting pair. This result makes no claim about a
parent position or an empty board.

Let `P` be the accepted 54-pair `L_row` certificate. Remove the pairs
`{b,e}`, `{c,h}`, and `{g,i}` to obtain the 51 exterior pairs `Q`, and reserve
the eight initially free cells

```
a=(11,8)  b=(13,8)  c=(13,9)  d=(12,9)
e=(14,7)  g=(14,8)  h=(14,9)  i=(14,10).
```

The checker regenerated all 1,040 literal Snaky placements. Of the 263
initially live targets, 255 contain a pair from `Q`; the other eight have
eight distinct traces in `K`. Both sufficient lower-right pairs
`{(12,11),(12,12)}` and `{(13,11),(13,12)}` are present in `Q`, so the browser
proposal's admission condition C holds. Every initially live target either
contains a pair from `Q` or has a trace of at least two cells in the reserved
domain. For each
of the eight possible first local Maker entries, the supplied fresh Breaker
reply must either hit that trace or leave one of the displayed fresh local
pairs inside it. A ninth row checks the response to an unmatched exterior
entry: take `d` and restore the original three core pairs. These conditions
are checked directly against every full target, not inferred from the
browser's exposure table.

While waiting, Breaker answers exterior pair entries by their mates. Thus
every touched exterior pair has a Breaker endpoint, and all eight reserved
cells remain free. An exterior claim cannot complete a target protected by
such a pair, nor a target still needing reserved cells. A first local claim
cannot win either, because each target without an exterior pair still needs
at least one other reserved cell. The local response and pair replacement
are therefore legal after any amount of exterior play. Previously touched
exterior pairs may be discarded because their targets are already blocked;
all untouched pairs remain free.

After commitment, use the ordinary mate-or-filler rule on the surviving
exterior and local pairs. Maker can never complete a protecting pair: if its
mate were already Maker-owned, the proposed new cell would already be
Breaker-owned. A needed free mate supplies a legal reply even near board
exhaustion. If no reply remains, the last Maker claim has still not completed
any protecting pair. Additional Breaker fillers only block more targets.

The finite check also explored every committed local state, allowing
arbitrary outside moves and arbitrary local fillers as an overapproximation.
Wins were checked immediately after each Maker claim, before a reply. Across
the nine commitments, the replay checked 2,700 local states, 8,316 Maker
entries including outside moves, 16,452 arbitrary filler transitions and
657 final local Maker claims. All twelve adversarial controls passed, testing
old-color preservation, domain freshness, overlap, the lower-right admission
condition, row completeness, stale responses,
owned pair endpoints, uncovered targets, and immediate local wins. This
local replay supplements the full-target product argument; it does not
replace the arbitrary-exterior-history proof above.

The single run used 0.041195 process CPU seconds and 0.214470 guarded wall
seconds, with peak child RSS 26,804,224 bytes. Child 46537 exited zero with no
guard events; cumulative swapouts remained 18,693,886. The limits were
8 internal CPU / 25 internal wall seconds, inside the unchanged
10 CPU / 30 wall / 100 MiB guard. No solver, search constructor, or catalog
was imported. The unexecuted 19×126 reuse pass remains paused and is not a
dependency of this proof.

The immutable receipts are the [launch](../verification/lcap_k8_controller-launch.json),
[preflight](../verification/lcap_k8_controller-preflight-01.json),
[guard report](../verification/lcap_k8_controller-guard.json) and
[execution binding](../verification/lcap_k8_controller-execution.json).
SHA-256 bindings:

- Verifier: `3e526e80082e733216301de30dbd052d898e10f38dc713dd8269ebf9b9dc3535`.
- Result: `6923ff233b8b7fa0faeaecf65c03118eccf7c6e5f2f12739d1581d70409630cf`.
- Launch: `02eea9f29365efc3d99547ba10fbdb6c64ecf3f303f2d75091e849fb572061d1`.
- Guard: `eab8ef5fe9fc1712b6b6cb4cd9ea8d3030af78584428df6f330c2bc2ae2d028a`.
- Execution: `09e88938e4294d119f5f8afa4eaf347940daa573af69a13779698b45947891b9`.
