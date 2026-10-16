# Complete defenses at the two continued endpoints

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py continued_endpoint_defenses --output /tmp/continued_endpoint_defenses-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once. Breaker has a complete ordinary
physical defense at each exact continued endpoint below, with Maker to move
on the 10×10 board. Cell IDs are `10*y+x`. All existing ownership is retained.

```text
E52 (17+17):
M = 22 32 37 42 43 44 45 46 47 53 57 63 67 75 76 78 84
B = 12 31 33 34 36 38 52 54 55 56 58 66 68 73 74 77 94

E53 (18+18):
M = 22 32 37 41 42 43 44 45 46 47 51 57 61 67 75 76 78 84
B = 12 31 33 34 36 38 50 52 53 55 56 58 66 68 71 74 77 94
```

Reserve the six fresh cells `R={16,17,18,26,27,28}`. The saved report gives
a perfect matching of every fresh cell outside R: 30 pairs at E52 and 29 at
E53. Before the first Maker entry into R, Breaker always takes the outside
mate. There is no discretionary filler and no claim in R during this phase.

On the first R entry use this complete table, then retain every still-fresh
outside pair and install the two displayed local pairs:

| Maker | Breaker | New pairs |
|---:|---:|---|
| 16 | 17 | 26–27, 18–28 |
| 17 | 16 | 18–27, 26–28 |
| 18 | 27 | 16–17, 26–28 |
| 26 | 27 | 16–17, 18–28 |
| 27 | 17 | 16–26, 18–28 |
| 28 | 27 | 16–17, 18–26 |

The local table protects `{16,17}`, `{16,26,27}`, `{17,18,27}` and
`{18,27,28}`. Every initially live full Snaky contains one of these four sets
or one of the reported exterior covering pairs. The full covering implication
was checked against independently regenerated 432 literal Snakies, including
all crossing targets and all retained old Maker stones.

During the waiting phase each outside pair is untouched or contains one
Maker and one Breaker stone. A fresh outside claim therefore has a fresh
mate. A target protected by an outside pair cannot be completed before its
mate response; a target protected by R still contains at least two untouched
R cells. The first R claim also cannot complete such a target.

For each target the checker independently enumerates every orientation of
every consumed outside pair that meets it. Omitted pairs are disjoint from
both the target and R, so cannot change its completion or a contained
protector's freshness. After every possible first R claim/reply, any surviving
target contains a fresh retained outside pair or a fresh local pair. The
remaining global matching is total. Its mate invariant prevents a Snaky on
every subsequent Maker claim, including the final claim before Breaker's last
response. Even if Maker exhausts all outside pairs first, all six R cells
remain for the switch and two further paired rounds.

| Checked quantity | E52 | E53 |
|---|---:|---:|
| Fresh cells / all first entries | 66 | 64 |
| Initially live full targets | 85 | 68 |
| Exterior covering pairs | 22 | 20 |
| Total exterior pairs | 30 | 29 |
| Targetwise outside histories | 6,209 | 3,788 |
| Live-history switch checks | 3,198 | 2,310 |

All 12 switch commitments and nine rejection controls passed. The controls
reject lost old colors, missing entries/mates, occupied or overlapping pairs,
a failed local guard, and a lost full crossing target.

This does not lift backward to the original two 11+11 frontiers. The accepted
prefix proof shows that certain Breaker replies are forced **if Maker chooses
the displayed continuation**. It does not force Maker to make those claims.
Other Maker choices at earlier positions are unexamined here. These defenses
refute the proposed winning continuation at its reached endpoints; they do
not resolve either 11+11 ancestor or the empty board.

Evidence and execution:

- Checker `verification/continued_endpoint_defenses.py`, SHA256
  `cee9f08d63d4a0e8a28c18967da1917504d2e975a95b7310aa43cdf1c26ed187`.
- Full report `verification/continued-endpoint-defenses-01.json`, SHA256
  `77095635e6b24b225506937d660d5be09e58467228e34969ecb04135e7cde80e`.
- The adjacent `.receipt.json`, preflight, launch, guard, execution and logs
  preserve exact source/input/runtime hashes and command.
- Child 57884 exited 0; 0.0640 process-CPU seconds, 0.2207 guarded wall
  seconds, 21.6 MiB peak RSS, no pressure events. The gate used watcher53736,
  idle59.93%/57.20%, with cumulative and direct swapouts stable at18,791,118.
  Limits were12 internal/15 outer CPU seconds,45 internal/60 guard wall
  seconds and150 MiB, one thread at nice19. No retry or source edit occurred.

The finite audit can be reproduced from `board_size` with a fresh report path:

```sh
python3.12 -B reproduce.py continued_endpoint_defenses --output /tmp/continued_endpoint_defenses-publication.json
  --output /tmp/continued-endpoint-defenses-fresh.json
```
