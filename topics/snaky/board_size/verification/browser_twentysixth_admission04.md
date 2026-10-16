# Browser04 round26: A52 admission and waiting interface

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentysixth_admission04 --output /tmp/browser_twentysixth_admission04-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once. A52 is the accepted original P52
state with only Maker 32 and Breaker 33 removed. All other ten Maker and ten
Breaker cells remain fixed. No complete A52 outcome is claimed.

The finite checker regenerates all 432 physical Snakies. It checks the exact
160 live targets, the 14 revived by freeing33, and the two targets still missed
by naively adding pair32–33 to the P52 construction. It then transcribes the
35 proposed admission rows. For each first entry `u`, Breaker takes33; the
declared 36 outside pairs are fresh, disjoint, and total off the reserved
six-cell right component. Every surviving full target contains an outside
pair or one of the four independently checked right guards. Each of the six
right entries is also checked as a complete physical matching commitment.
The released-pair ledger retains every live physical incidence.

The 80 initially fresh cells partition into 16 waiting pairs, six right cells,
and a 42-cell domain D. The 35 admission entries S lie in D. Its remaining
seven entries are `{13,14,23,24,33,53,54}` and remain unresolved.

The arbitrary-history claim is restricted to the stated waiting policy.
Maker entries in a waiting pair receive their mate. Right entries use the
total six-cell controller, then its pair replies. No move is made in D until
its first actual entry. Every admission row retains all 16 waiting pairs and
changes pairs only within S; it does not borrow a previously occupied cell.

The checker validates all 55 ordinary right turn-boundary descriptions and
all their legal Maker claims, including final claims. It separately validates
the three possible types of protector for every physical target in every
admission row: an untouched D pair, an unchanged waiting pair, or a right
guard. This factorization accounts for arbitrary interleavings without
enumerating a large cross product. A consumed waiting pair permanently hits
its target with Breaker; an untouched one is fresh. Right guards remain safe
in every enumerated right history. Before admission, each revived target
still needs the unclaimed cell33. Thus no outside history is erased, and no
unstated filler move is allowed. The even-sized total pair/right domains
also supply legal responses through exhaustion.

The separate physical forcing check uses three full Snakies:
`{32,33,43,44,45,46}`, `{44,45,46,47,53,54}`, and
`{13,23,33,43,44,54}`. It enumerates all legal Breaker deviations in the
proposed force-and-fork trees. This gives necessary reply sets at first13,
23,33,53,54, and after `M33/B32,M13`. Their fresh requirements lie entirely
in D, so prior allowed waiting histories cannot change those requirements.
No restriction is claimed at first14 or24. These are necessary reply
conditions, not a complete A52 outcome.

The report is `browser_twentysixth_admission04.json`, SHA256
`0520e70ef225c078d0667d1f0ada0d8888aef9f5327de4a38a387acd25016872`.
All 35 rows, their 210 right switches, and all 160 live targets passed. The
55 right-history descriptions include 78 post-Maker checks and 48 final
claims. Twelve rejection controls and one positive final-claim control passed.
At first 13 and 23, each physical tree excludes 74 replies and checks 5,698
forced responses and 5,550 final fork replies. First 33, 53, and 54 each have
78 immediately losing replies. After `M33/B32,M13`, the checker excludes 74
replies through 5,550 final fork cases.

Child 71438 exited 0 after 0.148344 CPU seconds and 0.424489 guarded wall
seconds, with a process-family peak of 28,934,144 bytes and no guard events.
The verification guard admitted it at 35% usable memory and 53.97% CPU idle.
The source, interpreter, input/report hashes and exact command are bound in
`browser-twentysixth-admission04-01.execution01.json` and its launch record.
No retry or search was used.

The limits were four internal CPU seconds, 25 internal wall seconds, five
outer CPU seconds, 30 guard wall seconds, and 100 MiB RSS, with nice 19 and one
thread. Reproduction command with a fresh output path inside the same guard:

```sh
python3.12 -B reproduce.py browser_twentysixth_admission04 --output /tmp/browser_twentysixth_admission04-publication.json
  --output verification/browser_twentysixth_admission04.json
```
