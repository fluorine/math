# Scope and novelty: Snaky on 15×15 within 24 claims

This note uses the public-source audit recorded on **15 October 2026**
(Europe/Amsterdam) and the exact source revisions below. No new literature
survey was performed for this publication. The 24-move certificate passed
independent computational verification, exact reconstruction, and the complete
Lean 4.34.1 theorem and axiom audit, as recorded in
[`RESULT-15X15-24.md`](RESULT-15X15-24.md#lean-kernel-verification).

The precise advance is an explicit strategy on the empty **15×15 board within
24 actual Maker claims**, improving the height-25 bound of the pinned public
15×15 certificate. The rules are unchanged: Maker first, alternating fresh
single-cell claims, the exact six-cell Snaky, all D4 orientations and
translations, with the winning Maker claim included in the count.

## What the pinned sources establish

| Source | Revision | Relevant comparison |
|---|---|---|
| [Trevor Morris, snaky-15x15](https://github.com/gotrevor/snaky-15x15/tree/b18ed32473a6a22ebfdda98da62d61b8b1590c1e) | `b18ed32473a6a22ebfdda98da62d61b8b1590c1e` | Public 15×15 Maker win; its supplied card root has height 25. Also supplies a 17×17 strategy within 20 moves and a 9×9 Breaker result. |
| [Nándor Sieben, Snaky](https://github.com/nandorsieben/Snaky/tree/a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa) | `a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa` | Earlier 20-move sequence. |
| [OpenAI mathematics repository](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a) | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` | Earlier 21-move result. |
| [Bounds tracker](https://github.com/bigospeedrun/site/blob/000c32d3249b7d7bbde0278ba62cb51a576bfd60/src/lib/other-bounds.json) | `000c32d3249b7d7bbde0278ba62cb51a576bfd60` | Its 15 October snapshot still listed 20 for family 187 and distinguished the 15×15 board result from the move bound. |

Morris's [15×15 result note](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/docs/notes/snaky-15x15.md)
states the public Lean result as a Maker win without a move-count theorem.
The comparison with 25 is specifically to the inspected certificate, whose
8,671 cards are preserved unchanged as
[`reference/gotrevor-15x15-cards.txt`](reference/gotrevor-15x15-cards.txt),
SHA-256 `94fc96c8e9a7bbd99748f8668fd8ba22519fe9ea771ec76fe1c3ab94ee283084`.
It is not a claim that the upstream authors proved 25 optimal or presented 25
as their principal theorem. Their [results and next questions](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/docs/notes/snaky.md)
provide the board-size context.

After that audit, this project's separate **19-move result on 17×17 and the
infinite plane** became public in
[`shjvandekamp/math`, commit `32d7cca4d7d9b0cb9a39742d744127f3feba8d28`](https://github.com/shjvandekamp/math/tree/32d7cca4d7d9b0cb9a39742d744127f3feba8d28/topics/snaky).
That stronger infinite-board bound is preserved. A 24-move result on the
smaller 15×15 board addresses a different board-and-move tradeoff.

## Contribution and limits

The new construction retains complete Maker history while reusing sound local
cards. The compact certificate contains **89 newly constructed cards and 8,645
retained cards from Morris's 15×15 source**. The consulted 20-move and 19-move
catalogs contribute no retained cards. The complete source mapping and hashes
are in [`certificate/snaky15x15-24.map.json`](certificate/snaky15x15-24.map.json);
attribution and licenses are recorded in
[`reference/README.md`](reference/README.md).

The claim is the reproducible improvement of this pinned 15×15 certificate
from 25 to 24 under the same rules. The bounded source audit does not establish
worldwide priority or exhaustive absence of another 24-move strategy. This
work claims neither an improvement of the public infinite-board bound nor a
smaller Maker-winning board. It does not show 24 is optimal, exclude a
23-move strategy, or turn failed construction searches into game lower bounds.
