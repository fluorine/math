# R_gap first-reply searches

Publication scope: this is a curated research note. Large search decks,
solver logs, and unrun adapters named in the historical text remain outside
this compact package. Included finite receipts and the Lean theorem sources
are distinguished in [the closeout guide](../README.md).


The exact physical R_gap position has 26 Maker and 26 Breaker stones. After
Maker (6,3), the accepted acquisition leaves three first replies unresolved:
(5,3), (8,2), and (9,2). These experiments retain every old stone on the 14×14 board.

The first B(5,3) run stopped at its 300-process-CPU-second limit. It found no
applicable root, so that state remains **UNKNOWN**. It produced 1,264 new
ordinary cards. Independent verification passed for all 37,404 library cards
and 275,280 inside-reply cases in 10.68 seconds. The exported header is still the
inherited 17×17, height 19 result; it is not a 14×14 theorem.

The run used one thread at nice 19, 300.71 process CPU seconds and 304.06 guarded
wall seconds. Child peak RSS was 666,976,256 bytes; the 650 MiB guard recorded no
pressure event. Files `rgap-b53-search*` preserve the exact launch, physical
state, result and deck; `rgap-b53-audit*` preserve independent acceptance.

The accepted library may support subsequent distinct-state searches. Failure
of any bounded search does not prove a Breaker win, a lower bound, or failure
of all strategies.

The distinct B(8,2) run used the accepted 37,404-card pool. It reached the
650 MiB RSS cap after 38.43 guarded seconds and was stopped before writing
its result or deck. No new mathematical claim follows. The guard receipt
is saved under `rgap-b82-search*`; a smaller source basis is being considered
before any further query. The cap has not been raised.

After reviewing that memory failure, the lead scheduled one changed experiment
using the original 36,120-card base plus the 20-card local pack. The full
physical B(8,2) state and all resource caps were unchanged. This run completed
300.68 process CPU seconds in 305.36 guarded seconds without pressure events,
returning UNKNOWN. Its 37,383-card output includes 1,243 cards newly emitted
relative to that input pool. The independent all-card audit passed. These
cards may overlap the earlier B(5,3) additions; no unique-union count is claimed.
See `rgap-b82-base-search*` and `rgap-b82-base-audit*` for the exact evidence.

The remaining first reply B(9,2) received one distinct query with that smaller
basis and the same caps. It also remained UNKNOWN after 300.72 process CPU
seconds / 304.96 guarded seconds, with no pressure events and 650,690,560 bytes
sampled peak RSS. Its 37,564-card library contains 1,424 additions relative to
the input. Independent replay accepted every card and 275,267 inside replies
in 10.47 guarded seconds. The header remains inherited empty17/height19.
Exact evidence is under `rgap-b92-base-search*` and `rgap-b92-base-audit*`.
No unique union count across the three searches is claimed.
