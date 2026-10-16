# Checked 63-pair physical interface and conditional switch

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentysecond_maker01 --output /tmp/browser_twentysecond_maker01-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once. The report is
`verification/browser_twentysecond_maker01.json`, SHA256
`f06ccf683b1aa33e8342863a13783be80f85b6a4a83761bd8926ea04f3e6ad55`.
The reviewed source remained unchanged at
`830dd76c8a121a777e9ecb033bcb6dda00f1dbe7f1a7c9f075696efb52837b9e`.
No search or solver ran. This verifies a partial defense and one exact history,
not a complete defense at the initial state.

The input is the accepted exact R_gap+M(6,3)/B(5,3) state with 27 Maker and 27
Breaker stones, including the old anchors (3,11) and (9,11). It is bound through
`verification/browser_twentieth_maker01.json` and its pinned source and
dependencies. All 1,040 literal full Snakies are independently regenerated.
The new browser response and its full transcript are pinned as proposal data.

The checked matching removes exactly two of the accepted 41 pairs:
`{(13,9),(13,11)}` and `{(13,10),(14,10)}`. It adds the 24 explicitly listed
new pairs, giving 63 disjoint fresh pairs. The audit checked the complete
196-cell ownership/endpoint inventory and the exact 16 unmatched fresh cells,
then classified every full target. All 253 previously protected live targets
stay protected; the new total is 370 of 385. The complete uncovered set equals
the 15 explicit full body/hook witnesses T1–T15 in the report. Old Maker cells
remain recorded in every physical target.

Each exception has at most one unmatched fresh cell. Consequently
no new pair disjoint from all 63 fixed pairs can cover even one exception.
This concerns adding pairs to this exact matching. It does not exclude a
different matching, adaptive sharing of paired cells, or a physical Maker
strategy. The ordinary mate-or-fresh-filler invariant protects only the 370
covered targets and checks Maker completion before any reply, including a
final claim. An exception can still end the game.

The switch was checked after these exact physical rounds:

| Maker | Breaker |
|---|---|
| (10,13) | (9,13) |
| (11,13) | (11,14) |
| (12,13) | (12,14) |
| (13,13) | (13,14) |
| (13,12) | (14,12) |

The first four replies must be the current listed mates. The fifth is an
override: taking the old mate (13,11) would instead let Maker complete the
literal T15 on its next claim (14,12). With the proposed reply (14,12), retire
pairs that contain actual new claims, replace the still-fresh pair
`{(14,9),(14,11)}` with `{(13,11),(14,9)}`, and retain every other pair.
The cells (12,12) and (14,11) remain physically free.

The audit checked freshness and immediate wins at every round, retained
the full 32+32 resulting colors, and tested all 370 initially protected targets
against the actual new Breaker stones or the new 57-pair matching. It checked
every live incidence of both nontrivially released pairs and all 1,040 targets
at the resulting state. There are 330 live targets, with 318 protected and
exactly 12 remaining exceptions; T3, T4 and T15 are killed. The 18 unmatched
fresh cells are the original 16 plus (12,12) and (14,11). No counterfactual
Breaker stone or projected pass is allowed. This switch is certified only
for the stated history; it is not an all-entry policy at the original 27+27
state.

All nine focused rejection controls passed. They cover forgotten old colors, overlapping or
occupied pairs, a dropped full residual, an incorrect early mate, the missing
new protector, an incompatible retained old pair, and a false full-defense
label. No repeat was performed.

Child 58968 exited 0 after 0.132951 process CPU seconds and 0.428551 guarded
wall seconds. Peak observed child RSS was 46,596,096 bytes (44.4 MiB), with
no pressure events. Limits were 8 internal CPU / 25 internal wall seconds,
10 outer CPU / 30 guard wall seconds and 100 MiB, one nice19 thread.
The two fresh watcher-53736 samples had 57.15% and 51.82% idle; sampled and
direct swapouts stayed at 18,791,118. Full launch, guard, logs and hashes are
bound in `verification/browser-twentysecond-maker01-01.receipt.json`.

Reproduce from the board-size directory with a fresh output path, using the
same reviewed resource guard and caps:

```sh
python3.12 -B reproduce.py browser_twentysecond_maker01 --output /tmp/browser_twentysecond_maker01-publication.json
```
