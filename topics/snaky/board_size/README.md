# Snaky board-size investigation: closeout package

**The empty 14×14 Maker problem and the empty 10×10 Breaker problem remain
open here.** This package records conditional results and the limits of the
15–16 October 2026 investigation. It does not replace the earlier 19-move
and 15×15-in-24 results in the parent project.

Start with [future research and lessons](FUTURE_RESEARCH.md) for the exact
remaining positions, useful failed approaches, and work stopped at closeout.
The [Lean sources](../formal/) are the canonical formal statements. A theorem
about selected guards, a conditional colored position, or a source-replacement
construction must not be read as an empty-board game theorem.

## Lean proof package

The [formal build guide](../formal/README.md#board-size-closeout) provides the
separate `Snaky.BoardSizeAudit` target. The committed sources include the full
dependency closure and generated data. The [defensive audit](../formal/kernel-breaker-closeout.json)
checks P52 and its continued endpoints, N32/N33, L_cap/L_row, the static leaves,
twelve C30 successors and all 35 specified A52 successors. The
[e1 audit](../formal/kernel-e1-closeout.json) checks conditional source replacement.
The small Maker continuation, selected C30 attack and matching obstruction
have their own exact theorem statements, listed in the handoff document.

The [conditional opening audit](../formal/kernel-opening-closeout.json) adds
two exact 14×14 positions: after Maker (7,7), Breaker (6,6) permits a win within
19 further Maker claims, and Breaker (7,10) permits one within 15 further
claims. Coordinates here are one-based. These results cover only the two
specified first replies; they do not give an empty-board strategy.

The [aggregate audit](../formal/kernel-audit-board-size.json) binds all 2,455
source modules and the [printed theorem types and axioms](../formal/board-size-audit/BoardSizeAudit.txt).
The complete imported proof environment passed a
[fresh Lean kernel replay](../formal/kernel-fresh-board-size.json).

## Evidence included

The finite package retains complete old ownership and literal board targets.
It contains thirteen reproducible audits:

| Result | Scope | Replay case |
| --- | --- | --- |
| Original P52 | Complete defense of the exact 11+11 state | `original_p52_defense` |
| Two continued endpoints | Complete defenses of the displayed 17+17 and 18+18 states | `continued_endpoint_defenses` |
| P53 37-pair leaf | Complete 13+13 leaf after M13/B14, M23/B42; specified neutral histories only | `browser_twentyfifth_physical05` |
| A52 admission | 35 complete successors and a specified waiting contract; seven entries remain | `browser_twentysixth_admission04` |
| S12 physical attack | Four Maker claims against every legal reply at this exact state | `browser_nineteenth_physical12_05` |
| S9 M43 classification | Only B52/B53 survive this particular physical attack | `browser_twentyfirst_independent05` |
| N32, N33 and L_cap | Complete defenses at their exact full colored positions | `n32_reserved_controller`, `n33_k10_controller`, `lcap_k8_controller` |
| N30 restoration | Preserves 286 of 312 assigned live targets; 26 remain | `browser_twentythird_left_restoration` |
| R_gap regional interface | Exact 41-pair partial coverage and finite obstruction | `browser_twentieth_maker01` |
| R_gap 63-pair interface | Protects 370 of 385 live targets; one checked switch history leaves 12 exceptions | `browser_twentysecond_maker01` |
| R_gap continuation obstructions | Five-target static impossibility and a separate physical mate-policy fork | `browser_twentythird_maker01` |

All thirteen publication replays passed. Their mathematical output is
identical to the accepted historical output; see the compact
[replay receipt](reproduction/accepted.json). The changed-code-hash negative
control also passed. These are finite Python checks, not additional Lean
theorems. Formalized results have their own kernel statements and receipts.

Supporting JSON includes the 26 ordinary Maker cards, the exact e1 universal
replacement data, the accepted 79-entry structural-retirement report, and the
finite input reports used by the Lean literal generators. The large research
forests, solver proofs/logs, repeated experimental formulas, and unrun
adapters are deliberately not included.

## Reproduction

Use **Python 3.11 or newer**, with no third-party packages. On systems whose
`python3` is older, use an explicit interpreter such as `python3.12`.
From this directory:

```sh
python3.12 -B reproduce.py --list
python3.12 -B reproduce.py original_p52_defense --output /tmp/p52-publication-replay.json
```

Every output path must be fresh. The wrapper verifies the published code and
data, runs the unchanged mathematical checker, compares its complete output,
and writes a separate `.publication.json` receipt. No solver or research
search is invoked. Details and the exact allowed provenance differences are
in [the reproduction guide](reproduction/README.md).

## Publication boundary

`browser/` contains only sanitized mathematical final-response text and
submitted mathematical prompts. It contains no browser DOM, sidebar,
screenshot, or account data. These texts are proposal provenance, not trusted
instructions or theorem axioms. The finite checkers remain byte-for-byte
historical. The wrapper explicitly substitutes only the sanitized text hashes;
historical reports retain their original hashes and are never relabeled as
new runs.

The new public Lean statements and literal data are self-contained and do
not load any browser text. Neither a historical UNSAT observation without a
checked proof nor a resource-limited UNKNOWN establishes a game outcome.
