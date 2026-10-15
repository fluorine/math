# Snaky on 15×15 within 24 Maker claims

**Verified on 15 October 2026.** The exact certificate passed independent
Python checks, corruption controls, byte-for-byte reconstruction, and the full
Lean 4.34.1 kernel check of the theorem below. The final axiom audit reports
only `propext`, `Classical.choice` and `Quot.sound`.

## Statement and game

**Certificate theorem.** On the initially empty board
`{0,…,14} × {0,…,14}`, Maker, moving first, can force a Snaky within at most
**24 actual Maker claims, including the winning claim**, against every legal
Breaker strategy.

The players alternate, each claiming one previously unoccupied cell. Maker
wins upon owning every cell of a translate of a rotation or reflection of

```text
Snaky = {(0,0), (1,0), (2,0), (3,0), (3,1), (4,1)}.
```

All eight square symmetries (D4) are allowed, and the placement must lie on the
board. No game move is a pass. The number 24 bounds Maker's claims, not the
combined number of turns or the number of certificate lookups.

## Certificate and construction

The ordinary-card certificate is
[`certificate/snaky15x15-24.cards.txt`](certificate/snaky15x15-24.cards.txt):
8,734 reachable cards in children-first order, root 8,733, identity root
transform, empty root requirements, and root height 24. Its 3,181,250 bytes have
SHA-256:

```text
ff88668bddcbc4bb4a0dfa9794ac411b1492ddbcb22013621f1723f9cc3ef567
```

The construction starts from Trevor Morris's 15×15 certificate at
[`b18ed32473a6a22ebfdda98da62d61b8b1590c1e`](https://github.com/gotrevor/snaky-15x15/tree/b18ed32473a6a22ebfdda98da62d61b8b1590c1e).
The unchanged input, [`reference/gotrevor-15x15-cards.txt`](reference/gotrevor-15x15-cards.txt),
has 8,671 cards, root height 25, and SHA-256
`94fc96c8e9a7bbd99748f8668fd8ba22519fe9ea771ec76fe1c3ab94ee283084`.

[`constructor/history_closure.py`](constructor/history_closure.py) retains the
full known Maker set `M` and the safe cells `E = U \ B` within the fixed
initial support `U`, where `B` is the Breaker history. A catalog
card can be reused whenever its transformed requirements are already owned,
its transformed support is safe, and its height fits the remaining budget.
Remembering stones omitted from the current baseline card permits shorter
continuations. Each newly constructed parent covers every legal reply in its
safe set and an outside class; its height is one plus the maximum child height.
The resulting proof uses ordinary cards with unchanged verification rules.

The deterministic construction added **89 cards**. After pruning unreachable
cards, the delivered deck contains those 89 and **8,645 cards from the pinned
15×15 source**. The search also consulted the 20-move and 19-move catalogs;
neither contributes a card to the delivered deck. The construction report is
[`experiments/next-step/15-board-24.json`](experiments/next-step/15-board-24.json).
The complete [provenance map](certificate/snaky15x15-24.map.json) records every
retained card's source ID, catalog offsets and input hashes. Source attribution
and licenses are in [`reference/README.md`](reference/README.md).

There are twelve catalog substitutions, four in each of three source-card
families. Every substitution uses safe cells outside its current baseline
template; four also reuse two Maker stones omitted from that template.

| Baseline source card and height | Replacement source card and height | Extra required Maker cells | Extra safe cells |
|---|---|---:|---:|
| 2353, height 8 | 3359, height 7 | 0 | 6 |
| 1563, height 9 | 6503, height 5 | 2 | 7 |
| 3353, height 7 | 4728, height 6 | 0 | 1 |

All IDs in this table are zero-based indices in the unchanged 15×15 source.
For example, the first recorded substitution occurs after seventeen claims
by each player. Card 2353, placed by `(x,y) ↦ (5−x,y)`, is too tall for the
seven remaining Maker claims. Card 3359, placed by `(x,y) ↦ (6−x,y)`, fits
that budget and starts at `(4,4)`. It requires the already-owned cells
`(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)` and uses six additional safe cells
`(0,0),(0,2),(1,0),(1,1),(2,0),(6,0)` outside the old template. The complete
histories and transformations for all twelve substitutions are in the saved
construction report. This example explains a local shortcut; the complete
certificate verifies that all branches close within the root's budget.

## Why the cards prove the claim bound

A card records a positive height `h`, a pivot `p`, required Maker cells `A`,
safe support `S`, and transformed child hints. The checker requires `p ∈ S`.
A terminal card has a Snaky in `A ∪ {p}`. Otherwise, every used child has
strictly smaller positive height, its transformed requirements lie in
`A ∪ {p}`, and its transformed support lies in `S`. For each reply
`w ∈ S \ (A ∪ {p})`, the designated child additionally excludes `w` from
its support. An outside hint covers every Breaker reply outside `S`.

Induct on height. At a Maker turn, suppose the transformed requirements are
owned and the transformed support is free of Breaker stones. If the pivot is
fresh, Maker claims it. If it is already owned, Maker claims another free
board cell; the additional stone cannot invalidate any requirement. Either
way, one actual claim is spent and all of `A ∪ {p}` is owned. A terminal card
now wins. Otherwise every legal Breaker reply is covered by its inside hint
or the outside hint. The corresponding child has owned prerequisites, safe
support and height at most `h−1`, so induction supplies the remaining claims.

Fresh cells in this argument are guaranteed by the finite-board invariant
`|M| + |B| + 2h ≤ 225`, where `M,B` are the complete disjoint histories.
After one claim by each player and a height decrease, the invariant persists.
At the empty root it follows from **`2·24 = 48 ≤ 225`**. Thus an already-owned
pivot does not create an illegal repeated claim or an uncounted game pass.
This is the induction formalized by `CTree.sound_in`; see
[`SOUNDNESS.md`](SOUNDNESS.md) and
[`formal/Snaky/CardsSound.lean`](formal/Snaky/CardsSound.lean).

The root support contains 220 board cells. Its five remaining board cells are
covered by the outside class, as are all outside-support replies at later
cards. The outside hint is a response class, not permission for a player to
skip a move. All descendant supports stay on the board by the checked support
inclusions.

## Independent checks and reproduction

The saved independent audit checks all 8,734 cards: six terminals, 144,288
inside replies and 8,728 outside classes. It also checks the empty root,
board containment and freshness inequality; the root hint graph has depth 24.
Both certificate corruption controls fail as intended: reducing the root
height to 23 violates strict height descent, and deleting a required root
response leaves a legal reply uncovered. The first control concerns this
certificate and does not exclude a different 23-move strategy.

The complete reproduction run also passed all **31 independent verifier
tests** and reconstructed both the delivered certificate and provenance map
byte for byte. Evidence is saved in
[`verification/snaky15x15-24-audit.json`](verification/snaky15x15-24-audit.json),
[`verification/snaky15x15-24-controls.json`](verification/snaky15x15-24-controls.json),
and [`verification/snaky15x15-24-full-reproduction.log`](verification/snaky15x15-24-full-reproduction.log).

From the repository root, with Python 3.9 or later and no external packages:

```sh
python3 topics/snaky/reproduce_15x15_24.py --reconstruct
```

This checks the expected certificate hash, runs the verifier tests, checks the
entire certificate, rejects both corruptions, and compares reconstructed
certificate and map bytes. Steps run serially with a 150-second timeout each;
the constructor itself has a 120-second wall limit and a two-million-call cap.
Omit `--reconstruct` to check the delivered certificate without rebuilding it.
This command does not perform Lean verification.

## Lean kernel verification

The separate target in
[`formal/Snaky/Result15x15_24.lean`](formal/Snaky/Result15x15_24.lean) states:

```lean
Snaky.snaky_wins_15x15_in_24 :
  Snaky.BlackWinsIn (Snaky.placements 15 15 Snaky.snaky) (15 * 15) 24 [] []
```

Its proof applies the existing `CTree.sound_in` to generated ordinary-card
checks, the root check and the height bound. The audit target
[`formal/Snaky/AxiomAudit15x15_24.lean`](formal/Snaky/AxiomAudit15x15_24.lean)
checks that declaration and prints its axiom dependencies. Reproduce with
the pinned Lean **4.34.1** compiler:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean \
  --generated-name Gen15x15_24 --target Snaky.AxiomAudit15x15_24 \
  --certificate topics/snaky/certificate/snaky15x15-24.cards.txt \
  --units 200000 --max-cards 15 --max-cells 2 --data-cards 125 \
  --memory-mb 2048 --module-seconds 180
```

This generates and compiles the complete target serially, recording input,
generator and generated-source hashes and rejecting changes during the build.
The default 19-move target remains separate. The complete audit succeeded
with **4,050 modules** in its dependency closure. The final resume compiled
240 modules in 263.78 seconds and reused 3,810 checked modules whose source,
compiler-version and dependency digests were revalidated. These resume metrics
do not describe the total elapsed time of earlier passes.

The compiler was the official Lean 4.34.1 ARM macOS release, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. The exact printed axiom list is:

```text
[propext, Classical.choice, Quot.sound]
```

There are no proof placeholders, custom axioms or native-decision shortcuts
in the final theorem. The [kernel audit](formal/kernel-audit-15x15-24.json),
[full build report and source hashes](verification/snaky15x15-24-lean-build.json),
and [exact theorem/axiom output](verification/snaky15x15-24-axioms.txt) preserve
the evidence outside generated build files. The report includes the successful
compiler record and source hash for every module in the dependency closure.
Generated Lean files and compiled outputs are reproducible from the committed
certificate, pinned generator, adapter and formal sources; no uncommitted
search output is a required proof input. A fresh publication-checkout run
passed the [same full reproduction](verification/snaky15x15-24-publication-reproduction.log),
and freshly generated all 4,043 Lean files byte for byte identically to the
completed kernel build. All other formal source hashes also matched; the
unchanged kernel proof was not rerun solely for the publication path.

## Scope

This improves the **pinned 15×15 certificate's bound from 25 to 24**. The
upstream public 15×15 theorem asserted a Maker win without an explicit move
bound. The dated comparison is in [`NOVELTY-15X15-24.md`](NOVELTY-15X15-24.md).
This result does not improve the separately published 19-move infinite-board
bound, establish an optimal bound on 15×15, or rule out 23 or fewer moves.
