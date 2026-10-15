# Snaky strategy bounds

Two independently checked and Lean-verified results, organized by move bound:

| Subtopic | Board |
|---|---|
| **[19 Maker moves](19-moves/)** | Infinite square board and 17×17 |
| **[24 Maker moves](24-moves/)** | 15×15; improves the pinned 25-move certificate |

Each subtopic collects its proof note, exact certificate, Lean theorem,
verification evidence, source credits and reproduction commands. Both results
passed independent checks, corruption controls, exact reconstruction and the
Lean 4.34.1 kernel audit.

## Common game conventions

Maker moves first. The players alternate, each claiming one previously
unoccupied cell. Maker wins by owning a translated, rotated or reflected copy
of the exact six-cell shape
`{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`. All eight square symmetries are allowed.
Both bounds count **Maker's own claims, including the winning claim**.

The different board sizes are part of the statements. Neither result is an
optimality claim. These are AI-assisted mathematical contributions offered
for public scrutiny; each subtopic states its relationship to prior work.

## Shared definitions, tools and sources

- [Game and certificate specification](SPECIFICATION.md)
- [Mathematical soundness argument](SOUNDNESS.md)
- [Construction tools](constructor/README.md)
- [Independent verifier](verification/README.md)
- [Lean build guide](formal/README.md)
- [Pinned sources, attribution and licenses](reference/README.md)

The proof artifacts and shared tools remain at their documented paths, so the
published links and repository-root reproduction commands continue to work.
The eighteen-move research is paused; no eighteen-move strategy is claimed.
