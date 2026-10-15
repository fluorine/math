# Snaky move-bound novelty audit

Audit date: 15 October 2026 (Europe/Amsterdam). Completed before strategic searches.

## Intended theorem

On the initially empty board Z², Maker has a strategy against every legal Breaker
strategy that occupies a Snaky by at most Maker's nineteenth move. Maker moves
first. Each turn claims exactly one previously unclaimed cell. Breaker only
blocks; completion of Breaker's own shape is irrelevant. The winning move counts.
The target is a translated, rotated or reflected copy of
`{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`. Maker may own other cells: “exact six-cell
shape” specifies the winning subset, not that Maker's entire position has size six.

## Public baseline

The strongest public upper bound located is **20 actual Maker moves**. No public
strategy meeting 19 or fewer moves was located in the sources and searches below.
Missing search results are not evidence that a problem is globally open.

| Primary source | Pinned revision and commit date (UTC) | Relevant claim |
| --- | --- | --- |
| [gotrevor/snaky-15x15](https://github.com/gotrevor/snaky-15x15/tree/b18ed32473a6a22ebfdda98da62d61b8b1590c1e) | `b18ed32473a6a22ebfdda98da62d61b8b1590c1e`, 2026-10-12 13:34:44 | `snaky_wins_17x17_in_20`; separate 15×15 winning result |
| [nandorsieben/Snaky](https://github.com/nandorsieben/Snaky/tree/a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa) | `a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa`, 2026-10-08 01:20:40 | `proof-sequence-20.html.gz` |
| [bigospeedrun tracker](https://github.com/bigospeedrun/site/blob/88d1855ba6843586579d8e031389ad94a475bb41/src/lib/other-bounds.json) | `88d1855ba6843586579d8e031389ad94a475bb41`, 2026-10-15 10:22:45 | Family 187: baseline 21, improvement 20; evidence label “claimed” |
| [openai/math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a) | `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, 2026-10-12 21:55:24 | *Snaky in 21 Maker moves*, manuscript 2026-09-25; infinite-board formalization scope in `lean/docs/187.md` |
| [erebos-labs/snaky-bounded-lean](https://github.com/erebos-labs/snaky-bounded-lean/tree/239dae48c0f8e227595424a9318126e01508df3a) | `239dae48c0f8e227595424a9318126e01508df3a`, 2026-10-09 02:59:29 | Lean soundness code for Sieben's strategy on the infinite lattice; “no claim of a new strategy, optimality, or a smaller finite-board bound” *(added in a later check)* |
| [KaiaSage/snaky-demo](https://github.com/KaiaSage/snaky-demo/tree/db62e51521944b0a7101062567352532efcec069/research/snaky20), branch `claude/research-snaky-20` | `db62e51521944b0a7101062567352532efcec069`, 2026-10-08 23:07:29 | Independent draft 20-move certificate; its “Toward 19” notes say “The plan plus win-in-1 is refuted at 19” *(added in a later check)* |

Inspected the requested historical revision
`1173345102f9d39472e38db0fdd810f7bfd4ed4e` (2026-10-09 14:33:47 UTC), including
`lean/Snaky/Result17.lean`, and the current version of that file. It states
`BlackWinsIn (placements 17 17 snaky) (17 * 17) 20 [] []`. The certificate has
1,738 cards, converted from Sieben's 1,510 situations. Root 1737 has height 20.
The source reports kernel evaluation and no proof placeholders; this audit is
source inspection, not a local Lean rebuild.

The [17×17 note](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/docs/notes/snaky-17x17.md)
explicitly says 20 is not a proved minimum. Replacing root height 20 by 19 is
rejected by its existing checker because a referenced child has height 19. This
rules out that relabeling, not other strategies or sharper uses of the data.
The [15×15 result](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/docs/notes/snaky-15x15.md)
does not improve the Maker move bound. Its 8,671-card certificate and the 9×9
Breaker result concern board size. Neither merely reproducing 20 moves nor
finding a board smaller than 17×17 achieves this research target.

## Search record

Queries submitted on the audit date:

- `github gotrevor snaky-15x15`
- `github nandorsieben Snaky`
- `github bigospeedrun site other-bounds.json`
- `github openai math snaky`
- `Snaky "19" "moves"`
- `Snaky "20" Sieben 2026`
- `"Snaky" "19-move"`
- `"Snaky" "19 Maker"`
- `"Snaky" "20 moves" Maker`
- `"Snaky" "nineteen"`

Primary repository pages, the tracker, OpenAI's formalization scope, and
gotrevor's notes were inspected; GitHub commit API metadata pinned versions.
Results for 19 were mostly unrelated. This is a bounded audit, not a guarantee
of exhaustiveness. If a matching public result is found, retire the exact target
and audit a materially stronger one before further experiments.

## Required difference

A successful artifact must prove a uniform bound of 19 on actual Maker moves
against arbitrary legal Breaker replies on Z², including replies outside finite
support. A smaller certificate, altered labels, a favorable sample line, or a
finite unsuccessful search does not establish this. The current target remains
active on the evidence above.
