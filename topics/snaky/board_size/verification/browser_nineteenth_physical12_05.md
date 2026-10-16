# Independently checked physical counterstrategy at S12

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_nineteenth_physical12_05 --output /tmp/browser_nineteenth_physical12_05-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once: Maker wins from the exact S12 in
four further claims against every legal Breaker reply. This is a conditional
physical result, not an empty-board result.

The accepted S13 certificate is
`browser-eighteenth-full-pairing05-01.json` (SHA256
`c8679a8fab93fdbbbd749981d7ec89fbcf43441b617e55fa94cd9ae554e5cbd0`).
Remove only its final M32/B1. This leaves S12, with Maker to move:

- Maker: 11, 21, 31, 37, 44, 45, 46, 47, 57, 67, 75, 84.
- Breaker: 14, 24, 34, 36, 38, 43, 55, 56, 58, 74, 77, 94.

Cell IDs are `10*y+x` on the fixed 10 by 10 board. The original nine stones of
each color and the actual prefix M11/B14, M21/B43, M31/B24 remain unchanged.

The nineteenth browser05 proposal starts M41. If Breaker claims 51, Maker
claims 1; otherwise Maker claims 51. In the latter case the four disjoint
fork triples are (0,10,20), (2,12,22), (40,50,60), (42,52,62). Two Breaker
claims leave at least two untouched. In the former case the two disjoint
triples are (30,40,50), (32,42,52); the first reply51 touches neither, so the
second reply leaves one untouched. Maker claims the first untouched triple's
centre, then its left endpoint unless Breaker just took it, in which case
Maker takes its right endpoint. The ten distinct full Snaky witnesses are
declared in the independent checker and checked against all432 literal
placements, not against projected fragments.

`browser_nineteenth_physical12_05.py` independently binds the saved complete
source, validates the fork tables, and enumerates every legal physical
Breaker response: 75 first replies, 73 second replies per first, and71 third
replies per pair, for388,725 terminal branches. Each final claim must complete
its full declared Snaky immediately. No outside pass class or prescribed
Breaker response is assumed. The report stores each first/second reply row
and a deterministic streamed digest of all terminal branches. It also checks
all old colors and the69 remaining free cells at every terminal.

The accepted all-reply evidence is
`browser-nineteenth-physical12-05-01.json`, SHA256
`4ff192c91a7130bb21806fe470eb765221011f2e147fc3e4b5f4b9ef571a6c97`.
All75 first replies,5,475 second-reply nodes, and388,725 terminal branches
passed. The four-fork case always retained at least two untouched forks;
the two-fork case always retained at least one. All ten full witnesses were
literal Snakies. Every branch won on Maker's fourth claim with69 cells still
free. Seven rejection controls and one positive final-claim control passed.

Frozen checker SHA256:
`950513fff32dd56bc1a909460542487aaade3cffce1b86bf89fdb5d874e24d36`.
The single run used0.538594 CPU seconds and0.840040 guarded wall seconds;
child peak RSS was41,517,056 bytes, exit0, with no pressure events. It ran
nice19 with one native thread under8 internal/10 outer CPU seconds,
25 internal/30 guard wall seconds and100 MiB RSS. Full pins, command,
fresh preflight and guard output are bound by
`browser-nineteenth-physical12-05-01.execution.json`, SHA256
`2c66fa805835b9dd4fce7ce866486c67056a0d1185f396bec0c1b2111632cfb6`.
There was no search or solver call.

The S12 matching query was cancelled before any export, control run, or solver
process began. Its held preflight and cancellation record remain preserved.
This counterstrategy invalidates a complete Breaker defense allowing the
specified S12 position. The accepted M32/B1 successor is still Breaker-winning:
there,1 is already Breaker-owned and the pairing includes41–51, so the two
fresh alternatives used here are unavailable. No result at S9 with different
earlier replies, or at empty10, follows.

## Reproduce the independent check

From the repository worktree root, with Python 3.12 and no extra dependencies:

```sh
python3 -B topics/snaky/board_size/verification/browser_nineteenth_physical12_05.py --output /tmp/snaky-s12-audit.json
```

Use a fresh output path; the checker refuses to overwrite an earlier report.
It checks its pinned inputs before the finite replay and enforces an internal
8 CPU-second / 25 wall-second bound. The expected status is
`verified_conditional_S12_physical_Maker_win_in_four`.
