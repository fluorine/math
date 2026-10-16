# Browser05 round25: complete leaf and unresolved P53 interface

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentyfifth_physical05 --output /tmp/browser_twentyfifth_physical05-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed. This note does not claim a defense or
Maker win at the original P53 position. The accepted mathematical assertions
were unchanged by a one-character correction to the prompt-list delimiter;
the initial rejected report and source are preserved.

The checker binds the accepted original 11+11 P53 colors, the complete literal
432-target universe, and the browser's numbering of its 155 live targets. It
imports only frozen independent geometry, matching, and six-cell table helpers.

The first proposed positive result is the exact leaf after
`M13/B14, M23/B42`. Its 30 covering pairs and seven completion pairs form a
perfect matching of all 74 remaining cells. Every live physical target must
contain a fresh pair. The ordinary mate policy therefore protects it before
the response as well as after it: at the start of each round a pair is wholly
fresh or already contains Breaker. The final Maker claim is covered by the same
argument. No discretionary filler or resetting of an old color is allowed.
The audit also checks every surviving incidence of the six released pairs of
the older partial matching.

Nine specified neutral pairs are retained at this leaf. Their completed
exchanges commute with the two core rounds because they are disjoint from
13,14,23,42. Targetwise enumeration checks untouched and both consumed
orientations of every neutral pair touching each target, including Maker wins
before mate responses. Other neutral pairs cannot affect that target or the
core prefix. This proves precisely the stated neutral-interleaving class;
arbitrary histories on the other boundary pairs are not declared harmless.

The negative object is a physical attack after the prescribed `M13/B14,M23`.
It enumerates all 70 second replies outside `{22,31,42,51,52}`. Maker plays42,
forces31 through the full target `{31,32,42,43,44,45}`, then plays52 and forks
22/51 through two full targets. Every subsequent legal Breaker reply and final
Maker claim is checked. In particular, automatic B24 is unsafe. This does not
prove that B14 after the first M13 is unsafe, or that P53 is Maker-winning.

The remaining positive data are an exact decomposition, not a solved game.
Deleting pair53–54 from the accepted P52 framework leaves exactly four gaps at
P53. Closing their fresh support under the retained pairs yields 19 cells;
adding the reserved six-cell right switch and54 yields26. A total matching of
the other52 fresh cells protects81 targets. The other74 retain both their core
and outside requirements, with17 boundary pairs and nine neutral pairs. For
example `{50,51,61,62,63,64}` still requires outside cells63 and64. The checker
validates the safe pair-color interface but never evaluates the proposed
recurrence or searches for a policy.

The report is `browser_twentyfifth_physical05.02.json`, SHA256
`5af2a85e778f613d94757c1e8e27e68b5a1681b197b55e09919c5d23bdfb5ab6`.
The 37-pair leaf covers all 110 live physical targets. The obstruction checks
70 excluded replies, 5,110 subsequent forced-response cases, and 4,970 final
fork replies. The neutral-history check covers 1,385 targetwise histories,
10,278 pre-response checks, and 206 unblocked leaf checks. Eleven rejection
controls and one positive final-claim control passed.

Child 71591 exited 0 after 0.025801 CPU seconds and 0.217059 guarded wall
seconds. Its process-family peak was 26,361,856 bytes, with no guard events.
The root-approved verification guard admitted the run at 38% usable memory
and 58.15% CPU idle. The exact command, source/input pins, interpreter,
guard hash, and output are bound by
`browser-twentyfifth-physical05-01.execution03.json`. The earlier delimiter
failure remains in `.execution02.json` and `browser_twentyfifth_physical05.json`;
it occurred before any mathematical assertion was checked.

The limits were four internal CPU seconds, 25 internal wall seconds, five
outer CPU seconds, 30 guard wall seconds, and 100 MiB RSS, with nice 19 and one
thread. Reproduction from `board_size`, with a fresh output path and the same
verification guard:

```sh
python3.12 -B reproduce.py browser_twentyfifth_physical05 --output /tmp/browser_twentyfifth_physical05-publication.json
  --output verification/browser_twentyfifth_physical05.02.json
```
