# Snaky within 24 Maker moves on 15×15

[All Snaky results](../README.md) · [19 moves on 17×17 and the infinite board](../19-moves/)

**Maker can force the exact six-cell Snaky within 24 of Maker's own claims
on the initially empty 15×15 board, against every legal Breaker strategy.**
The winning claim is included. This improves the pinned source certificate's
bound of 25 on the same board; it does not establish optimality.

[Read the full proof note](../RESULT-15X15-24.md)
· [Exact certificate](../certificate/snaky15x15-24.cards.txt)
· [Lean theorem](../formal/Snaky/Result15x15_24.lean)
· [Kernel audit](../formal/kernel-audit-15x15-24.json)
· [Novelty and scope](../NOVELTY-15X15-24.md)

## Proof and verification

The certificate has **8,734 reachable cards**: 8,645 from Trevor Morris's
pinned 15×15 strategy and 89 new cards. The construction retains Maker's
history and safe cells omitted by the current tactical template, allowing
shorter continuations. The [proof note](../RESULT-15X15-24.md) explains the
soundness induction and gives a concrete shortening step.

- The [independent audit](../verification/snaky15x15-24-audit.json) checks
  every card, all 144,288 inside replies and 8,728 outside classes.
- All 31 verifier tests passed. Both [corruption controls](../verification/snaky15x15-24-controls.json)
  were rejected, and [reconstruction](../verification/snaky15x15-24-publication-reproduction.log)
  reproduced the certificate and provenance map byte for byte.
- Lean 4.34.1 checked the exact theorem below, with 4,050 modules in its
  dependency closure. Its only axioms are `propext`, `Classical.choice` and
  `Quot.sound`. See the [complete build evidence](../verification/snaky15x15-24-lean-build.json)
  and [exact theorem/axiom output](../verification/snaky15x15-24-axioms.txt).

```lean
Snaky.snaky_wins_15x15_in_24 :
  Snaky.BlackWinsIn (Snaky.placements 15 15 Snaky.snaky) (15 * 15) 24 [] []
```

## Reproduce from a clean checkout

From the repository root, using Python 3.9 or later and its standard library:

```sh
python3 topics/snaky/reproduce_15x15_24.py --reconstruct
```

For the complete formal proof, use the official Lean **4.34.1** compiler:

```sh
python3 topics/snaky/formal/build.py --lean /absolute/path/to/lean \
  --generated-name Gen15x15_24 --target Snaky.AxiomAudit15x15_24 \
  --certificate topics/snaky/certificate/snaky15x15-24.cards.txt \
  --units 200000 --max-cards 15 --max-cells 2 --data-cards 125 \
  --memory-mb 2048 --module-seconds 180
```

The [formal build guide](../formal/README.md) records the compiler provenance,
resource limits and resumable build behavior. The certificate, generator and
formal sources provide all required proof inputs; no search output is needed.

## Sources and scope

The [complete provenance map](../certificate/snaky15x15-24.map.json) identifies
every retained card and pins the consulted catalogs. Attribution and licenses
are in the [source record](../reference/README.md).

This is a move-bound improvement on 15×15. The separate
[19-move result](../19-moves/) applies to 17×17 and the infinite board.
Neither result proves an optimal bound or rules out a faster strategy.
