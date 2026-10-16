# Complete conditional Breaker defense at P52

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py original_p52_defense --output /tmp/original_p52_defense-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The original 11+11 P52 position is independently accepted as Breaker-winning,
with Maker to move on the full 10×10 board. This resolves one of the two
frontiers after S9/M43/B52-or-B53, M32/B33. It does not resolve P53, the position
before M32, S9, or the empty board.

Using cell IDs `10*y+x`, the exact permanent colors are

```
M = {32,37,43,44,45,46,47,57,67,75,84}
B = {33,34,36,38,52,55,56,58,74,77,94}
```

Reserve `R={16,17,18,26,27,28}`. The 29 covering pairs and seven additional
pairs in [the checker](../verification/original_p52_defense.py) form a perfect
matching of all 72 fresh exterior cells. Before the first Maker entry into R,
Breaker takes the exterior mate. There is no discretionary filler.

On the first R entry, use the following actual claim and fresh local pairs:

| Maker | Breaker | Remaining local pairs |
|---|---|---|
|16|17|26–27, 18–28|
|17|16|18–27, 26–28|
|18|27|16–17, 26–28|
|26|27|16–17, 18–28|
|27|17|16–26, 18–28|
|28|27|16–17, 18–26|

Retain all untouched exterior pairs and then use the total mate strategy.

The finite geometric claim is that each of the 146 initially live full
targets contains an exterior covering pair or one of
`{16,17}`, `{16,26,27}`, `{17,18,27}`, `{18,27,28}`. Each table row either
blocks each such guard or leaves a fresh listed pair inside it. These guards
are sufficient protection conditions, not physical winning targets.

This proves safety under arbitrary interleaving. An exterior pair is untouched
or already has one actual Maker endpoint and one actual Breaker endpoint.
The six reserved cells stay pristine until the switch. Before every Maker
claim, any unblocked full target still contains two fresh protected cells;
the claim cannot finish it. After the switch every unblocked target has a
fresh covering pair. The total matching supplies a legal response through
exhaustion, including the final Maker claim. Old colors are never reset.

The reviewed independent checker regenerated all 432 literal D4 placements,
checked all 78 first entries, and enumerated 14,816 targetwise exterior pair
histories, including both orientations. Pairs disjoint from a target and R
cannot affect that target's completion or its local protector, so this finite
quotient covers all exterior histories. There were 6,582 live-history switch
checks and 13 rejection controls. All passed once.

The accepted [report](../verification/original-p52-defense-01.json) has SHA256
`51d0885027969cbe0fafdeae9b009c187ad6438c7a6b84fbcf6d38ab1a9c4df1`.
Checker SHA256 is
`dc4881010c5150a9dff2421fc5a9899cef183f2d1e866ebfb5e14b6f922a93d1`.
The [execution record](../verification/original-p52-defense-01.execution01.json)
binds the launch, fresh resource gate, logs, report and unchanged sources.
Child 60165 used 0.075924 CPU seconds and 0.214856 guarded wall seconds,
with 25,231,360-byte peak RSS and no pressure events. Limits were 8 internal
and 10 outer CPU seconds, 25 internal and 30 guarded wall seconds, 100 MiB,
one thread at nice19. All ten artifact/input hash bindings were checked by
the lead after execution. No Lean or empty-board theorem is asserted.

For reproduction, run the checker with a new `--output` path under the same
resource guard and caps recorded in the execution's launch file. Existing
reports are immutable. The earlier endpoint checkers and reports remain intact.
