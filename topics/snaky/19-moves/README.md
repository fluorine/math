# Snaky within 19 Maker moves

[All Snaky results](../README.md) · [24 moves on 15×15](../24-moves/)

**Maker can force the six-cell Snaky within 19 of Maker's own moves on the
initially empty infinite square board, against every legal Breaker strategy.**
The winning claim is included in the 19. The same certificate proves a win
within 19 moves on the empty 17×17 board.

[Read the proof note](../output/pdf/snaky-note.pdf)
· [Markdown manuscript](../MANUSCRIPT.md)
· [LaTeX source](../publication/snaky-note.tex)
· [Result and verification scope](../RESULT.md)
· [Novelty audit](../NOVELTY.md)
· [Exact certificate](../certificate/snaky19.cards.txt)
· [Lean theorems](../formal/Snaky/Result19.lean)
· [Kernel audit](../formal/kernel-audit.json)

Maker moves first. Each player claims one previously unclaimed cell per turn.
A winning set is any translation, rotation or reflection of
`{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`; Maker may own additional cells.

## Contribution and prior work

The dated public-source audit found 20 moves as the strongest prior public
bound. This construction combines Nándor Sieben's twenty-move strategy with
local tactics from Trevor Morris's 15×15 work, building on OpenAI's earlier
Snaky result. It retains the actual Maker history and safe cells that the
current tactical template has forgotten, producing a uniform nineteen-move
strategy. The contribution is the new composition and its verified bound;
the imported tactics and proof infrastructure are explicitly credited in the
[provenance record](../reference/README.md). The note also cites the classical
Snaky literature and two related public projects not used here: Erebos Labs'
Lean soundness code for Sieben's strategy and KaiaSage's independent draft
20-move certificate.

The result is an upper bound. It does not prove that nineteen is optimal.
Novelty is relative to the [15 October 2026 audit](../NOVELTY.md), rather than a
claim that every unpublished or unindexed result has been ruled out.
This is an AI-assisted mathematical contribution offered for public scrutiny.

## What is verified

- The [exact certificate](../certificate/snaky19.cards.txt) has 3,468 reachable
  cards. The independent verifier checked all 61,040 inside reply obligations,
  3,456 universal outside classes, terminal shapes and strict move-count descent.
- All 31 focused tests passed. Deliberately reducing the root bound or removing
  a required reply was rejected. Reconstruction produced identical certificate
  bytes. See the [verification evidence](../verification/README.md).
- Lean 4.34.1 kernel checked both
  `Snaky.snaky_wins_plane_in_19 : Snaky.PlaneBlackWinsIn 19 [] []` and
  `Snaky.snaky_wins_17x17_in_19`. Both depend only on `propext`,
  `Classical.choice` and `Quot.sound`. There are no proof placeholders,
  custom axioms or native decision shortcuts. See the
  [formal proof](../formal/README.md) and [kernel audit](../formal/kernel-audit.json).

The plane theorem handles every legal integer-coordinate Breaker reply
explicitly, including replies outside the certificate's finite support.
[Game conventions](../SPECIFICATION.md) and the [soundness argument](../SOUNDNESS.md)
explain the connection between finite data and the infinite game.

## Reproduce from a clean checkout

Python 3.9 or later and its standard library suffice for construction and
independent checking. No network or external Python packages are needed:

```sh
git clone https://github.com/shjvandekamp/math.git
cd math
python3 topics/snaky/reproduce.py --reconstruct
```

For the full formal proof, install the official Lean **4.34.1** compiler and run:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean --target Snaky.Audit
```

The [formal build guide](../formal/README.md) gives compiler provenance and resource
limits. It generates the proof modules from the committed certificate and
checks them serially; no mathlib is needed. Generated modules and binaries are
rebuildable outputs, not missing proof inputs.

The current PDF was built with XeLaTeX from TeX Live 2026; earlier versions
used Tectonic 0.15.0, which also uses the XeTeX engine. To regenerate it from
the included standalone LaTeX source:

```sh
tectonic --outdir topics/snaky/output/pdf topics/snaky/publication/snaky-note.tex
```

or run `xelatex` three times in `topics/snaky/publication`.

[Construction tools and mechanism](../constructor/README.md)
· [Pinned source data and credits](../reference/README.md)
