# Snaky within 19 Maker moves

## Established result

**Maker can force Snaky within 19 of Maker's own moves from the empty infinite
square board, against every legal Breaker strategy.** The same certificate
also gives a win within 19 moves on the empty 17×17 board.

Maker moves first, each turn claims one previously unclaimed cell, and the target
is `{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}` under translations, rotations and
reflections. The winning claim counts toward the 19.

The delivered certificate is `certificate/snaky19.cards.txt`:

- SHA-256 `baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e`.
- 3,468 cards, all reachable from root 3,467; root and longest dependency height 19.
- 249 protected root cells in `[0,16]×[0,16]`, with first move `(8,8)`.
- 61,040 checked inside responses and 3,456 universal outside response classes.
- 12 terminal cards, checked against the exact six-cell Snaky geometry.
- Empty root requirements and finite-board capacity `2*19≤289`.

An independent Python verifier, written from the mathematical semantics and
sharing no constructor checking helpers, accepted this exact file. Thirty-one
focused card, transcript and local-state tests passed. Mutations reducing the
root height to 18 or deleting a required root response were rejected.
`SOUNDNESS.md` proves that the checked finite implications yield a legal policy
on Z², including every reply outside the support. An independent adversarial
review found no gap in the shape, turn, support, occupied-cell or bound semantics.

Lean 4.34.1 also completed the full kernel check of this certificate and the
direct infinite-board soundness theorem. The resulting statements are
`Snaky.snaky_wins_plane_in_19 : Snaky.PlaneBlackWinsIn 19 [] []` and the
corresponding 17×17 theorem. Both report only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; neither depends on a proof placeholder,
custom axiom or native decision procedure. See `formal/kernel-audit.json` for
the exact theorem output and build evidence.

## Contribution and provenance

The construction combines Sieben's public 20-move strategy and tactics from
Morris's public 15×15 strategy. It retains full Maker history and a safe region
recording actual Breaker replies, allowing tactics to use safe cells discarded
by the current template. All 180 shortcut leaves use additional safe cells;
68 also use earlier Maker stones forgotten by the current template. The
successful run needed no zero-cost occupied-pivot steps or new certificate rule.

The compact proof contains 1,662 cards from the 20-move source, 1,653 from the
15×15 source, and 153 newly constructed cards. Exact source IDs, transforms and
construction commands are under `constructor/`. Credits are in
`reference/README.md` and `MANUSCRIPT.md`.

The 15 October 2026 audit located no public 19-move-or-better strategy and found
20 to be the strongest public upper bound. Novelty is relative to that documented
audit, not a guarantee that no unindexed result exists.

## Reproduce

```sh
python3 topics/snaky/reproduce.py
```

Add `--reconstruct` to regenerate from the pinned public inputs and require
byte-for-byte identity. No external Python packages or network are needed.
The final run passed all 31 tests and both corruption controls, and reproduced
the delivered certificate byte for byte.

For the full Lean kernel check, use the pinned compiler as described in
`formal/README.md`:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean --target Snaky.Audit
```

## Scope

No optimality, 18-move impossibility, or infinite-board lower bound is asserted.
Earlier search failure concerned a restricted construction mechanism. Nothing
from the later follow-on research is included in this nineteen-move publication.
