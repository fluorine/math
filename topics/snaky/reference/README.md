# Public reference certificate

`sieben-20-cards.txt` is copied unchanged from
[gotrevor/snaky-15x15](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/third_party/sieben/cards-17x17.txt),
revision `b18ed32473a6a22ebfdda98da62d61b8b1590c1e`, retrieved 2026-10-15.
SHA-256: `c15deef097541e2413cc543916e8d5773ffa398f5be66ca976c73f894c7fd832`.

The strategy is Nándor Sieben's 20-move proof sequence, building on OpenAI's
21-move strategy. Trevor Morris's repository contributes conversion into cards
and a Lean proof. Its upstream attribution and permission statement is in
[`sieben-UPSTREAM-README.md`](sieben-UPSTREAM-README.md), copied unchanged from
`third_party/sieben/README.md` at the same pinned revision. That notice records
Sieben's permission to publish the sequence and Lean proof in Morris's
repository; it is quoted as upstream provenance, not a new permission claim.
Its SHA-256 is `e737e4cb87402717fd5875b34521dce6a5b1af937481670e70ce23afbddb76dc`.
The Apache-2.0 repository license is retained as `gotrevor-LICENSE`. The original sequence is at
[nandorsieben/Snaky](https://github.com/nandorsieben/Snaky/tree/a0a36dd4edffdccdb7c4b14849c81e83dd6a25aa).

This reference is a baseline, not this project's final certificate or a new result.

`gotrevor-15x15-cards.txt` is the same revision's
[`cert/snaky-15x15-cards.txt`](https://github.com/gotrevor/snaky-15x15/blob/b18ed32473a6a22ebfdda98da62d61b8b1590c1e/cert/snaky-15x15-cards.txt),
retrieved 2026-10-15, 3,337,287 bytes.
SHA-256: `94fc96c8e9a7bbd99748f8668fd8ba22519fe9ea771ec76fe1c3ab94ee283084`.
It has 8,671 cards and root height 25; its local tactics are an additional pool
for construction experiments, not an improvement of the 20-move root bound.

The separate [24-move result on 15×15](../RESULT-15X15-24.md) improves this
pinned certificate's height-25 bound by a new composition of its tactics.
The delivered compact proof retains 8,645 original 15×15 cards and 89 newly
constructed cards. `../certificate/snaky15x15-24.map.json` attributes every
card and pins every consulted input; the source certificate stays unchanged.
This is a move-bound improvement on the same board, not a smaller winning
board or an improvement to the published infinite-board bound of nineteen.
