# Final certificate

`snaky19.cards.txt` is the complete declarative certificate, 1,365,722 bytes.
SHA-256: `baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e`.

Its root is card 3467, with no required Maker stones, height 19, first move
`(8,8)`, and 249 protected cells inside `[0,16]²`. All 3,468 cards are reachable.
Card indices are zero-based. Exact coordinates, D4 transforms, all required
reply hints and the universal outside hint are encoded in the file.

The format and semantics are specified in `../SPECIFICATION.md`; the mathematical
soundness argument is in `../SOUNDNESS.md`. Independent acceptance and negative
controls are recorded in `../verification/snaky19-compact-audit.json` and
`../verification/snaky19-negative-controls.json`. The audit path names the
constructor's identically hashed copy.

`../constructor/snaky19.compact_map.json` maps every final ID to its original
source or new construction ID. The proof reuses public cards credited in
`../reference/README.md` and contains 153 new history-specialized cards. Pruning
removes unused cards and changes IDs only. No generated execution trace is
needed to check this file.
