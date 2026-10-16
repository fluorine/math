# Next local questions for the accepted 63-pair interface

Publication scope: this is a curated research note. Large search decks,
solver logs, and unrun adapters named in the historical text remain outside
this compact package. Included finite receipts and the Lean theorem sources
are distinguished in [the closeout guide](../README.md).


This is a read-only mathematical assessment and execution proposal. No new
geometry audit, solver query, game search, or engine test was run. The separate
Browser01 prompt is `browser/01-twentythird-prompt.txt` (26,079 characters,
SHA256 `9b7922aa49d6ee95d89953cf9872bdb2e7de91922d9fb1e64ed9632962055985`).

**Closeout status:** the user subsequently requested that existing work finish
and research stop. The two T14 query sources below were prepared, but no
controls, exports, formula audits, solver calls or shallow searches ran.
These are unreviewed, unexecuted future-work sources, not accepted results.
There is no pending execution allocation for them.

The accepted input is `verification/browser_twentysecond_maker01.json`, SHA256
`f06ccf683b1aa33e8342863a13783be80f85b6a4a83761bd8926ea04f3e6ad55`.
Its exact five-round switch ends at a physical Maker-turn state S5 with
32 Maker and 32 Breaker stones. All old 27+27 colors remain. Its 57 fresh
pairs protect 318 of 330 live targets, preserving every initially protected
member of the 370-target family. Twelve explicit exceptions remain.

## Two concrete forced continuations

At S5, the full target

```
T14 = {(9,12),(10,12),(10,13),(11,13),(12,13),(13,13)}
```

has exactly two fresh requirements, `(9,12)` and `(10,12)`. Its other four
cells are actual Maker stones from the accepted history. Thus:

| Maker's next claim | Required Breaker reply | Full state afterward |
| --- | --- | --- |
| (9,12) | (10,12) | S5 plus precisely these two claims; 33+33 |
| (10,12) | (9,12) | S5 plus precisely these two claims; 33+33 |

Any different Breaker reply leaves the other cell free for an immediate full
T14 win on Maker's next claim. This forces the reply only after the specified
Maker choice; it does not force Maker to choose either entry or to follow the
preceding five-round history. The export/checker must still reject any earlier
Maker completion before allowing a reply.

The currently retained pairs send these Maker entries to `(8,10)` and
`(11,12)`, respectively. Therefore merely freezing the post-switch pairing
is already inadequate. This deduction needs no new search.

The preferred new experiment is one unrestricted full-physical static
matching query at each of these exact 33+33 states. Regenerate all 1,040
targets, retain every old color, discard only targets hit by actual Breaker
stones, and encode every pair of still-free cells occurring in a surviving
target. Do not fix the old 63 pairs, the post-switch 57 pairs, an upper/bottom
partition, or a selected target family. There are 130 physically free cells
after each forced reply; the live-target counts must be derived, not guessed.

Reuse the frozen `static_pairing.encode` interface with literal 196-cell IDs
`14*(y-1)+(x-1)`, plus the existing independent full-board geometry/pairing
checker. A separate binder must derive S5 from the accepted report and verify
T14's exact old/new ownership, freshness, unique reply and all permanent
colors. It must reconstruct the complete formula rather than trust the
producer's target list. Positive models require disjoint fresh pairs covering
every live full target. UNSAT remains an unproved restricted-class observation;
UNKNOWN and incomplete output remain unresolved.

Proposed bounded execution, after source review: export at most 5 CPU / 30
wall seconds, independent encoding/controls at most 10 CPU / 60 wall seconds,
one direct Z3 solve per state at 30 CPU / 120 wall seconds / 200 MiB guard
(150 MB solver, one thread, nice19), then one independent result replay at
10 CPU / 60 wall seconds. Keep the two states sequential and use fresh host
gates. No automatic retry or higher cap is part of this proposal.

An accepted matching would be a complete defense at its exact 33+33 leaf.
It can also provide cheap checked reuse: at S5, the same reply and matching
work for another fresh Maker entry that is neither the reply nor a selected
pair endpoint. This follows because physical target coverage depends on the
Breaker set and whole fresh pairs, not on assuming the original extra Maker
claim. Each reused row should be explicitly bound and checked. Do not infer
all 132 S5 entries, let alone all 142 initial entries, from two positive leaves.

## Prior work and non-duplication

The scoped source/artifact review found a completed unrestricted static query
at the initial 27+27 B(5,3) state, recorded in
`maker/rgap-entry-pairing-b53-result.json`, and the completed 42-entry isolated
bottom-strip table in `breaker/rgap_bottom_result.md`. They are distinct
questions; both gave unproved UNSAT observations. The accepted Browser01
twenty-second package is only the finite matching/switch audit. No query at
either new post-switch 33+33 state was found in the scoped records reviewed.

Do not rerun the initial static query, the isolated bottom table, the nine-cell
controller, or the accepted five-round switch. Do not solve a game containing
only the 15 exceptions while silently discarding the 370 protected targets:
that would not certify the physical repair. Likewise, separate per-exception
policies can conflict through shared cells and mate endpoints.

If these two matching questions do not close, a shallow actual-state game
query is a separate proposal. It must keep all 196 cells and all full targets,
include every legal reply and immediate/final Maker claim, and use the
unchanged engine only after an exact size/state adapter is reviewed. A small
selected-target game or an unreviewed projection is not a substitute. No such
query is authorized by this note, and no engine was run for this assessment.

## Preserved source-only integration

`breaker/rgap_t14_matching.py` exports either exact continuation with
`--entry-x 9` or `--entry-x 10`. Its SHA256 is
`0475853aa25d3171e87c04b4f47318c6de989c5b509e2b6b1e5ac4117d07517e`.
`verification/check_rgap_t14_matching.py` has SHA256
`8d520504c45c463c6453dd8c71d58305eaa92211f3ea1c1db6bb4f31774ea5db`.
Both bind the accepted report/source and all report input hashes. The producer
reuses `static_pairing.encode`; the independent checker imports neither it
nor the producer. It reconstructs all 1,040 literal targets, full colors,
the five exact exchanges, all 130 off-line responses to the chosen T14 entry,
every residual target clause and all 196 cell capacities. The older
10-board formula helper was not reused because it hardcodes 100 capacities.

The checker includes 13 planned controls: eleven rejection cases for lost
old colors, an altered prior response, a wrong T14 reply, fixed/projection
restrictions, missing targets/coverage/capacity above cell99, incomplete
models and false SAT coverage; plus signal-to-UNKNOWN and restricted-UNSAT
classification controls. None has been executed. Its positive path calls
the frozen independent `check_pairing.check(14, ...)` on the actual complete
model and emits the existing `snaky-static-pairing-v1` format. The planned
solver command is embedded in each future export with the limits above.

A later separately authorized shallow Maker experiment could reuse the
unchanged adapter pattern in `maker/browser_sixteenth_maker02_exact5.py`:
retain literal coordinates in a width15 mask, restrict available cells to
`[1,14]^2` minus actual Breaker stones, and call
`constructor/deeper_tactics.solve_deeper_tactics` with an empty catalog and
height5. Ordinary emitted cards would require independent all-reply checking.
That engine's outside-reply overapproximation makes a positive safe but a
bounded negative weaker than a full physical game conclusion. A proposed
60 CPU /120 wall /200MiB allowance per unresolved leaf would be a new
experiment, not a continuation of an authorized run. No shallow adapter
was written or tested here.
