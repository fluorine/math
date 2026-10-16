# N30 six-cell left restoration

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentythird_left_restoration --output /tmp/browser_twentythird_left_restoration-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once. This is an assigned-target
interface, not a complete defense of N30, N31, or the empty board. No Lean
acceptance is claimed. The report is `browser_twentythird_left_restoration.json`,
SHA256 `5416d11c9e8f11d3cff765f93c014da53f82717d909aa99451e87adc19495c5f`.

The exact N30 state is the accepted 30+30 parent in
`maker/fourteenth-n-repair-prefix.json`. The checker binds every old color to
that report, the submitted full N30/N31 states, and the independently checked
N32 state after the two recorded arrows. It also rechecks the accepted 54-pair
L_row certificate against all 1,040 literal 14-board targets.

The reserved pristine domain is

```
A0=(4,10), A1=(4,11), U=(2,10), V=(3,10), W=(3,9), Z=(3,11).
```

Release exactly the old pairs UV and WZ. Keep the other 52 pairs, including
F1={(2,8),(2,9)}, F2={(2,11),(2,12)}, F3={(3,7),(3,8)},
F4={(3,12),(3,13)}, and F5={(4,12),(5,12)}. The local obligations are
`A0A1`, `A0UV`, `WVZ`, and `A1VZ`.

| First Maker entry | Actual Breaker reply | Committed local pairs |
| --- | --- | --- |
| A0 | A1 | UV, WZ |
| A1 | A0 | VZ |
| U | A0 | VZ |
| V | A1 | A0U, WZ |
| W | A1 | A0U, VZ |
| Z | A1 | A0U, WV |
| Unmatched exterior entry while pristine | A1 | UV, WZ |

Before local entry, exterior pair moves receive their mates and the reserved
domain remains pristine. An unmatched global filler may activate this domain
only by the last row; it may not claim an arbitrary cell inside it. Other
components must have disjoint response supports. After commitment, every
still-free mate is taken when its partner is played; otherwise any actual
fresh filler is safe for these assigned targets. Earlier exterior pair
histories leave a permanent Breaker endpoint, so no later switch borrows an
unknown exterior cell.

The check reconstructs the six live UV exposures and twelve revived A1
targets, verifies every full witness, and records all unassigned live
targets. It checks all 136 fresh physical first entries and exhausts the
fixed local policy's reachable ownership states under exterior interleaving
and arbitrary committed fillers. It checks wins before a response and after
the final legal local Maker claim. An outside move in the finite quotient is
an overapproximation of a real outside claim, not permission to pass.

The result protects 286 of the 312 live full targets and retains every one
of the 280 targets covered by the original matching. The other 26 full
targets are explicitly unassigned. The seven commitment contexts contain
360 reached local color states, 876 post-Maker checks, 121 final local claims,
and 1,468 arbitrary-filler transitions. All fifteen rejection controls and
the safe-final-claim control passed.

The sole child, PID 63982, exited 0 after 0.1173 CPU seconds and 0.4357
guarded wall seconds, with 35,618,816 bytes peak across its process family
and no pressure events. Limits were 4 internal CPU / 20 internal wall
seconds, under the unchanged 5 CPU / 30 wall / 100 MiB guard, nice 19 and
one native thread. The fresh two-sample gate used the conservative 35%
idle threshold and stable sampled/direct swap counters. No solver, tactic
search, catalog load, or repeated audit was used.

The underlying reproduction command is:

```
python3.12 -B reproduce.py browser_twentythird_left_restoration --output /tmp/browser_twentythird_left_restoration-publication.json
  --output verification/browser_twentythird_left_restoration.json
```

The actual execution receipt is
`browser-twentythird-left-restoration-01.execution01.json`; its associated
launch and preflight records bind the runtime, unchanged guard, CPU launcher,
all input hashes, resource preflight and exact command. The reviewed and
executed source SHA256 is
`a2dff650530e915297eaccc59bfecc77b51c542a86375bcf9fc242c9c5729636`.
