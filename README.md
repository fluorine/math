# Mathematical notes

Research notes, proofs, and reproducible checks. Each contribution states its
relationship to prior work and the scope of its verification.

## Sensitivity versus block sensitivity

[Read the note](topics/sensitivity-separation/output/pdf/sensitivity-note.pdf)
· [Overview and reproduction](topics/sensitivity-separation/README.md)
· [Novelty audit](topics/sensitivity-separation/publication/NOVELTY_AUDIT.md)
· [Follow-up review and sharper comparison](topics/sensitivity-separation/publication/FOLLOWUP_REVIEW.md)

An elementary directed adaptation of classical first-difference coloring gives
a compact deterministic generator for the tournament-label condition in the
OpenAI family-132 construction. A companion theorem strengthens its coupled
sensitivity-profile estimates. The note proves that the actual
coherent-set maximum is seven for the fixed seed. Using this sharper bound
in both analyses improves the certified exponent from approximately
2.0154112468 to 2.0154115475 at unchanged dimension. The PDF includes the
sharper bound and comparison; the linked review records the follow-up
audit and its independently implemented certificate. Earlier independent
manuscripts in the ProveIt repository report larger exponents (about 2.0321
and 2.0271) and part of the same target/gate counting; the note cites them
and does not claim a competitive exponent.

These are AI-assisted mathematical contributions offered for public scrutiny.
The notes distinguish the additional arguments from inherited constructions,
routine consequences, and finite computational evidence. Historical priority
remains provisional; no literature-wide record or formal verification of the
new results is claimed.

## Snaky within 19 Maker moves

[Read the proof note](topics/snaky/output/pdf/snaky-note.pdf)
· [Full proof and reproduction](topics/snaky/README.md)
· [Lean kernel audit](topics/snaky/formal/kernel-audit.json)
· [Novelty audit](topics/snaky/NOVELTY.md)

A 3,468-card strategy forces the exact six-cell Snaky within nineteen actual
Maker claims on the empty infinite square board, and also on 17×17. It combines
Sieben's twenty-move strategy with tactics from Morris's 15×15 work, retaining
full play history and safe cells discarded by earlier templates. The dated
audit located twenty as the prior public move bound.

The certificate is independently checked, reproduced byte for byte, and fully
checked by Lean 4.34.1, including a direct theorem for every legal infinite-board
Breaker reply. The repository includes the mathematical argument, exact data,
construction code, independent verifier, formal sources, negative controls and
source attribution. No optimality claim is made.

The separate [24-move proof on 15×15](topics/snaky/RESULT-15X15-24.md) improves
the pinned height-25 certificate on that smaller board. Its 8,734-card proof
is independently checked, reproduced exactly, and fully verified by Lean
4.34.1. The [dedicated kernel audit](topics/snaky/formal/kernel-audit-15x15-24.json)
records the exact bounded theorem and its standard axiom dependencies.

## Effective cylinder covers of a regular tetrahedron

[Read the mathematical note](topics/cylinder-covering/output/pdf/cylinder-covering-note.pdf)
· [Full proof and reproduction](topics/cylinder-covering/README.md)
· [Lean proof and kernel audit](topics/cylinder-covering/formal/README.md)
· [Exact verification](topics/cylinder-covering/verification/secant-report.md)
· [Novelty and source comparison](topics/cylinder-covering/NOVELTY.md)

An explicit cover by 20,000 triangular cylinders has normalized total base area
below 0.499922. A quartic overlap identity and an explicit finite secant buffer
prove coverage of the whole closed tetrahedron, with exact count, mesh/error
bounds and independently certified rational area intervals. The package also
contains a sharp finite enclosure theorem in a specified class.

The published comparison uses the audited source sufficient ranges and count
conventions; it is not global optimality over all covers or all new instances
of generic methods. The primary finite-cover theorem is formalized in Lean,
including actual geometry, effective count/error estimates and the complete
numerical interval. The package includes the independent exact-arithmetic
checks, kernel audit, negative controls, compact generators and pinned source
attribution. The comparison and restricted-class optimality arguments remain
separately identified written proofs. No human referee review is claimed.

## Three overlapping VIX windows in a finite activity market

[Read the mathematical manuscript](projects/vix-overlap-consistency/MANUSCRIPT.md)
· [Exact theorem and model](projects/vix-overlap-consistency/THEOREM.md)
· [Lean verification](projects/vix-overlap-consistency/VERIFICATION.md)
· [Novelty audit](projects/vix-overlap-consistency/NOVELTY.md)

An explicit family of ordinary SPX/VIX call panels has a compatible filtered
law for every one- and two-window subpanel, but none for the full three-window
panel in one fixed finite activity-schedule market. The same standing SPX panel,
information rules and admissible state space apply throughout. The exact
separation margin is `(1−30ε)/32` for every real `0≤ε<1/30`.

The complete finite-model theorem is checked in Lean 4.34.1, including the
ordinary-quote bridge, positive stock martingale, all diagonal and tower rows,
explicit witnesses, common bounds and the stated pairwise tests. The project
includes exact certificates, a pinned one-command verifier and an independent
statement audit. Novelty remains provisional. The theorem does not establish
inconsistency in unrestricted SPX/VIX markets or executable arbitrage.
