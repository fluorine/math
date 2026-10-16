# Snaky board-size research: results, open frontiers, and lessons

This is the closeout handoff for the 15–16 October 2026 investigation.
**Maker on the empty 14×14 board and Breaker on the empty 10×10 board remain
open in this work.** No further broad search is running or authorized by this
document. Saved proposals are future work, not a queue to execute after
closeout.

The game is ordinary alternating fresh single-cell play, Maker first, with no
passes. Maker wins immediately on completing a translated rotation or
reflection of `{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`, including on the final
legal claim. The physical 10×10 and 14×14 hypergraphs contain 432 and 1,040 targets.
Ten-board records normally use zero-based `10*y+x` IDs. Fourteen-board records
normally use physical `(x,y)` coordinates in `{1,...,14}². A saved state, frame,
and complete old ownership take precedence over an informal branch name.

## Proof status

Keep three kinds of evidence separate: Lean kernel theorems, independently
checked finite certificates with a stated lifting argument, and experimental
observations. The presence of a `.lean` file or a successful Python check is
not proof that the final Lean theorem compiled. Each row below states its
exact verification status and the limits of its conclusion.

| Claim or package | Status at closeout | Exact scope |
| --- | --- | --- |
| Earlier 19-move result | Kernel checked; [audit](../formal/kernel-audit.json) | Empty infinite board and empty 17×17; preserved prior result. |
| Earlier 15×15 result in 24 moves | Kernel checked; [audit](../formal/kernel-audit-15x15-24.json) | Empty 15×15, not 14×14. |
| Two conditional 14×14 openings | Kernel checked; [audit](../formal/kernel-opening-closeout.json) | Maker (7,7), Breaker (6,6) or (7,10): respectively 19 or 15 further Maker claims. One-based coordinates; only these exact first replies. |
| New 26-card continuation | Kernel checked; [receipt](../formal/Snaky/GenMakerCloseout/verification/kernel-accepted.json) | After M(12,6) and a nonexceptional actual reply at N30/N31, eight further Maker claims suffice. 119/135 and 117/133 initial replies are covered; 16 remain. |
| P52 and its two continued endpoints | All three real-game Lean defenses kernel checked; [audit source](../formal/Snaky/P52Audit.lean) | Exact original 11+11 P52 and the displayed 17+17/18+18 continued states; no backward lifting. |
| Selected C30 obstruction | Kernel checked; [receipt](../formal/Snaky/GenMakerCloseout/verification/c30-kernel-accepted.json) | Maker wins within ten claims in the selected 17-guard game only, not the physical S9 game. |
| Five-guard static obstruction | Kernel checked; [receipt](verification/rgap-matching-obstruction-kernel-accepted.json) | No globally fixed-point-free involutive mate covers the five guards; no adaptive-game conclusion. |
| Exact e1 source replacement | Lean semantic theorems kernel checked; [result](../formal/Snaky/E1Result.lean) | Same-domain pair replacement under the exact source and admission hypotheses, not an empty-board defense. |
| L_cap, L_row, S11, S13, post-M31/B41 and the new 37-pair leaf | Kernel checked; [defensive audit](../formal/kernel-breaker-closeout.json) | Each theorem concerns its exact full colored state. |
| N32, N33 and twelve C30 successors | Kernel checked; [defensive audit](../formal/kernel-breaker-closeout.json) | Complete ordinary-game defenses of the stated full positions, including outside interleavings and final Maker claims. |
| New N30 restoration and Browser 01 round 23 objects | Independent finite audits passed | Partial assigned-target preservation and precisely stated conditional obstructions; neither empty board nor parent game is resolved. |
| A52 admission rows | All 35 successor defenses kernel checked; waiting contract independently replayed | Each specified M(u)/B33 successor is defended. Seven admission entries remain; the complete A52 parent is open. |

The defensive audit contains 58 indexed endpoint cases across thirteen
declarations. Original P52 also occurs as A52 entry 32, so this is not a count
of 58 distinct positions. All depend only on standard Lean axioms. The
[printed theorem and axiom output](../formal/board-size-audit/BreakerAudit.txt),
[P52 output](../formal/board-size-audit/P52Audit.txt), and
[e1 audit](../formal/kernel-e1-closeout.json) record the precise statements.

The main new formal sources are [MakerCloseoutResult](../formal/Snaky/MakerCloseoutResult.lean),
[P52](../formal/Snaky/P52.lean), and [E1Result](../formal/Snaky/E1Result.lean).
The listed kernel receipts determine the release claims. The e1 result checks
463 valid row masks, three modes, six legal disjoint templates, and all 240
eligible sources from the full 432-target geometry. Its two semantic
replacement theorems use only `propext` and `Quot.sound`. In particular,
the Lean e1 replacement statement explicitly assumes its membership and
compatibility conditions; it must not be described as an unconditional game
winner. Older chronological notes may still say that a now-resolved child
was open. Use its later accepted report rather than combining those snapshots.

## Contributions worth retaining

**Ordinary Maker certificates.** New local cards were emitted, transported,
and independently checked with every inside reply and the universal outside
reply class. The compact 26-card [closeout package](verification/browser_twentythird_maker02_cards.json)
is particularly useful because it is small and binds an exact physical
response partition. Large research decks remain libraries of conditional
implications. An inherited 17×17 root header does not turn an enlarged deck
into a 14×14 proof, and additions from separate runs must not be summed as
though they were a deduplicated union.

The two opening results retain a compact union of 1,647 cards, with 389 exact
structural duplicates removed from their two dependency closures. Every card,
both physical placements, and both final game statements were kernel checked.
The [opening result source](../formal/Snaky/MakerOpeningResult.lean) fixes the
full initial ownership. Its bounds count claims after the initial Maker move,
so neither is an improvement of the empty-board 19-move theorem. The compact
deck regenerates the committed proof sources without the large search forests.

**Complete conditional defenses.** Full-target checks closed several exact
states that had resisted Maker searches: [L_row](verification/earlier_pairing_replay.json),
[L_cap](maker/lcap-k8-controller-proof.md),
[N33](maker/n33-k10-controller-proof.md),
[N32](verification/n32_reserved_controller.json),
[original P52](breaker/original-p52-defense.md), and
[both continued P52/P53 endpoints](breaker/continued-endpoint-defenses.md).
The earlier S11 also has a [32-pair defense](breaker/upstream11_physical_matching.md).
The final [P53 matching leaf](verification/browser_twentyfifth_physical05.md)
has 37 pairs covering every live target after `M13/B14,M23/B42` at original
P53. Nine specified neutral pair histories are allowed before and between
these rounds; the result is not a defense against arbitrary earlier entries.
These are useful negative branches for a future Maker proof. None lifts
backward merely because one chosen Maker route forces the displayed replies.

**Physical attacks and safe backtracking.** The exact S12 state has an
[all-reply four-claim Maker attack](verification/browser_nineteenth_physical12_05.md).
That invalidates the bad preceding B24 choice but preserves the valid S13
pairing and the alternative [post-M31 reply 41 defense](verification/post-m31-joint-matching-result-01.json).
The distinctions between these nearby states prevented a false ancestor claim.

**Useful partial interfaces.** The [R_gap 63-pair construction](verification/browser_twentysecond_maker01.md)
protects 370/385 live full targets at its exact 27+27 state. Its five-round
switch protects the original family and leaves 12 exceptions at 32+32. The
[N30 six-cell restoration](verification/browser_twentythird_left_restoration.md)
protects 286/312 targets with 52 exterior pairs and four local guards, preserving
all 280 targets previously covered there. Its 26 unassigned targets remain
explicit. Both results retain every full support cell and every old color.

**Structural retirement of source mechanisms.** The
[79-entry continuation audit](verification/resume_second_entry_result.md)
shows that every actual second-entry configuration below one fixed checked
9×9 source opening is replaceable by ordinary pairs within the same
admission class. Positive replacements cover UNKNOWN as well as OPEN traces;
the argument does not pretend to solve 79 physical game branches. The later
[universal e1 six-template result](breaker/e1_phase_template_universal.md)
handles a distinct source, all 240 eligible full sources, and 247 source-to-target
incidences, including different-source incidences. These results explain why
repeating sibling searches in those exact source families will not improve
admission existence under the same assumptions.

**Independent finite and encoding checks.** Literal geometry, ownership,
target-aware D4 transport, complete component supports, ordinary policy DAGs,
same-domain replacement, and several CNF encodings have separate checkers.
This makes the research reusable without trusting its construction heuristics.
The checks also exposed real errors: redundant claimed minimal guards,
incorrect fixture availability, omitted immediate wins, mistaken source
frames, and overly strong isolated projections.

## Precise open frontiers

### The physical 10×10 board S9 and P53 route

S9 is Maker
`{37,44,45,46,47,57,67,75,84}`, Breaker
`{34,36,38,55,56,58,74,77,94}`, Maker to move. There are 194 live targets.
The [physical M43 analysis](breaker/twentyfirst-physical-frontier.md) leaves
only B52 or B53, followed by M32/B33. Original P52 is now defended. The
remaining original P53 state is:

```
M={32,37,43,44,45,46,47,57,67,75,84}
B={33,34,36,38,53,55,56,58,74,77,94}
turn=Maker
```

P53 has 155 live targets. Its continued 18+18 endpoint is defended, which
closes that chosen continuation, not P53 itself. Static-root and all 78
first-entry reply-to-matching questions gave unproved restricted UNSAT
observations. The completed exact-five/six investigations were bounded
negative results in their declared tactic model. Neither observation proves
an unrestricted Breaker strategy or Maker win.

A useful future object is a complete physical P53 controller with explicit
waiting, entry, switch, and filler rules, or an all-reply Maker card using a
different acquisition. A new proposal should identify a particular missing
history or target interaction. Merely extending the same fixed matching or
repeating the settled endpoint questions is not a new mechanism.

The final P53 audit gives a more precise remaining interface. The P52 pairs
without 53–54, together with its right-side guards, protect 151 of P53's 155
live targets. The four exceptions close to a 26-cell domain; 26 exterior
pairs protect 81 targets, leaving 74 full crossing requirements. Those
requirements retain their outside cells. The proposed finite recurrence was
not evaluated. In particular, treating its core projections as physical wins
would invalidate the reduction. Following both old mates 13–14 and 23–24
loses to an explicit physical fork, while the alternative B42 leaf is defended.

The earlier A52 state is P52 with only Maker 32 and Breaker 33 removed.
Its [accepted admission interface](verification/browser_twentysixth_admission04.md)
closes 35 first entries by B33 and a complete successor defense. Sixteen
unchanged waiting pairs and the right controller permit their specified
arbitrary interleavings while the 42-cell admission domain stays pristine.
The seven remaining entries are `{13,14,23,24,33,53,54}`. Physical forcing
restricts replies at five of them, but neither these restrictions nor the
35 rows constitute a complete A52 defense. No arbitrary filler is authorized
by the waiting argument.

### N30/N31 on the physical 14×14 board

The exact states are in [the accepted prefix](maker/fourteenth-n-repair-prefix.json)
and [closeout card report](verification/browser_twentythird_maker02_cards.json).
N31 adds only M(4,10)/B(4,11) to N30. After M(12,6), the same sixteen replies
remain outside the checked continuation at both parents:

```
(11,5),(11,6),(11,8),(12,7),(12,8),(12,9),(13,4),(13,5),
(13,7),(13,8),(13,9),(14,5),(14,7),(14,8),(14,9),(14,10).
```

All full post-reply colored states are saved. A later exact card or complete
defense of an exception would reduce this frontier. The accepted N32 defense
does not resolve N30/N31. Conversely, the new six-cell left restoration only
removes its assigned local obstacle; a proposed combined defense must still
cover all remaining targets without overlapping response domains.

### R_gap and the compact bottom exception interface

The [R_gap state and three first-reply searches](maker/rgap-search-results.md)
retain the exact 26+26 parent. After M(6,3), B(5,3), B(8,2), and B(9,2) remain
the relevant physical branches of the checked acquisition. Their bounded
searches did not establish a root outcome. At the B(5,3) branch, the 63-pair
interface and 15 full exceptions are the most compact current starting point.

The [round 23 finite audit](verification/browser_twentythird_maker01.md) adds
two sharp constraints. After the accepted five-round switch, the forced
M(10,12)/B(9,12) branch has no fresh global matching even for five originally
protected targets. That selected obstruction itself admits a nine-entry adaptive local
table, so it is not a Maker-win proof. The opposite M(9,12)/B(10,12) branch
preserves the old family with 55 pairs but leaves nine full exceptions.

The compact [Lean matching obstruction](../formal/Snaky/RGapMatchingObstruction.lean)
formalizes only the five selected requirements `bf`, `abc`, `bcde`, `dfgh`,
and `cdgi`. Its mate function is a fixed-point-free involution on all natural
numbers, so partners outside the nine labels are permitted. It does not assume
a perfect matching on an odd nine-cell board. The [kernel receipt](verification/rgap-matching-obstruction-kernel-accepted.json)
records a successful Lean 4.34.1 check with only `propext`. The physical finite
argument and its adaptive counter-control remain separate.

On the left, following six stated old mates and waiting until a one-cell
exception appears loses to a physical fork. Just before the sixth reply,
only `(3,10),(2,14),(4,14)` prevent that fork. A fresh-matching repair after
any of these interventions must also release at least one of P50, P60, P61.
These are exact necessary dependencies, not a claim that any release suffices.
A useful next object would handle these earlier interventions and every newly
exposed full target. One cooperative switch history is inadequate.

## Approaches that did not resolve the goals

| Approach | What was learned | What does not follow |
| --- | --- | --- |
| Static and first-entry matching at S9 | Four forced-reply cases have literal six-target obstructions; the other 78 direct queries returned unproved UNSAT. | No unrestricted physical S9 outcome. |
| Full physical depth 3 S9 search | 37 conditional leaves were accepted; all 82 root entries remained unresolved. 943 oracle cutoffs and 16,149 exhaustive matching absences were distinguished. | A bounded oracle failure is not a game loss. |
| Fixed K20/K22 and selected C30 contracts | Explicit containment/allocation obstructions and the selected 17-guard C30 attack reject those formats. | The physical S9 game is not the stronger projected game. |
| Fixed permanent J and 47/48-cell quotients | Literal attacks exposed missing physical requirements and eventually refuted the particular actual J protocol. | A projected attack without full physical witnesses does not lift automatically. |
| Isolated 42-cell bottom reply table | All 42 queries gave unproved negatives for a conservative sufficient table; upper-pair reactions were intentionally omitted. | The coupled full 14×14 board defense is not ruled out. |
| Frozen 26/58/60/61 global admission formulas | Formula equivalence, dominance and model interfaces were checked; some restricted instances were observed UNSAT and others hit resource limits. | No empty 10×10 theorem or general static-pairing impossibility. |
| Larger conditional card libraries | Many valid local implications were saved; memory could dominate before a search began. | More cards, a successful construction, or an inherited root header is not a new root certificate. |

The 61-family CaDiCaL run with `reduceint=100` used its 900-CPU allowance and
remained UNKNOWN. The separately authorized 3,600-CPU attempt was stopped by
its 700 MiB RSS guard; the last native progress reported 2,276.22 CPU seconds.
It did not exhaust the full CPU allowance, and no exact final CPU measurement
was saved. Both executions remain in the local research snapshot under
`breaker/experiments/controller12-module-empty-01.cadical-cpu*-reduce100.*`;
large solver logs and formulas are deliberately omitted from this publication.
Neither can be described as an UNSAT proof. No restart checkpoint was available,
so the longer run paid for its repeated deterministic prefix.

## Preserved, unrun work

The [horizon-seven package](breaker/twentyfirst-frontier-exact7-unrun.md) is
documented source-only work retained in the local snapshot: generator, separate
generated engine/cache, exact P53 adapter,
and six focused controls. No test, query, ordinary-card export, or launch
manifest exists for horizon seven. Future use first needs the listed controls and
an independent ordinary-card audit of any positive output. Even a completed
bounded negative would apply only to that finite tactic model.

The [T14 static adapters](breaker/rgap-63pair-next-experiments.md) and
the local `verification/check_rgap_t14_matching.py` were stopped before any tests,
export, formula or solve. They retain the two full 33+33 states and allow an
unrestricted physical matching. The new five-target proof already excludes
the M(10,12)/B(9,12) static question, so running it now would add no mathematical
information. The opposite leaf remains a distinct adaptive/full-target
question; its 55-pair partial preservation must not be mistaken for a solution.

Other historical `proposal`, `unrun`, or `pending` files are not active jobs.
Before resuming, compare exact full colors, target universe, source frame,
quantifiers and prior receipts. Preserve the old formula and candidate when
changing an experiment; do not relabel an unexecuted artifact as checked.

## Methodological lessons and a disciplined next step

1. **Start with the acceptance path.** A positive ordinary card, full pairing,
   finite controller, or proof DAG should have a separate checker before a
   costly query begins. Keep the constructor out of the acceptance code.
   SAT needs a complete decoded model and every full target checked. UNSAT
   without a checked proof remains an observation about the encoded class.
   Bind compiler receipts to the exact module, command and proof object too.
   A receipt-filename collision during closeout was rejected, and every affected
   module was checked again using unique receipts. The final aggregate also
   passed a fresh-environment kernel replay before publication.
2. **Keep physical and virtual ownership distinct.** Bind source IDs, dispatch,
   transformations and every old color. For core coverage, retain every full
   eligible source and every source-to-physical incidence. Different-source
   witnesses matter; a shortened-only inventory can miss the decisive case.
3. **Reserve the entire response domain.** Pair/component coverage is not just
   the union of advertised targets. Unmatched support cells, filler choices,
   previously touched pairs, and switch prerequisites affect legality. A
   policy may be safe for a selected family while having a physical hole.
4. **Test Maker completion before responding.** Immediate wins can replace a
   proposed longer fork. Never allocate a reply after an immediate or final
   winning claim. No-pass and exhaustion semantics belong in both finite
   replay and the lifting proof.
5. **Prefer a discriminating finite object to a larger blind run.** A small
   forced-pair chain, targetwise history quotient, or explicit membership
   obstruction often explains a failure more usefully than another timeout.
   Retire source families when a same-domain replacement theorem removes
   their claimed advantage; do not keep enumerating equivalent siblings.
6. **Preserve fair partial work.** Save all positive certificates and explicit
   OPEN/UNKNOWN roots. Reuse a proof prefix only under exact state, source,
   formula and rule bindings. A replacement must cover UNKNOWN as well as
   OPEN cases; unresolved status cannot be treated as feasibility or failure.
7. **Measure construction separately from search.** The low-peak catalog
   remap and consuming variant reduced temporary duplication without changing
   semantics; construction measurements are not long-search guarantees.
   Sampled RSS, process CPU, host pressure and proof/output size are different
   constraints. Use a guard that owns the actual solver PID, not a wrapper
   whose detached child escapes measurement. Paused jobs still occupy slots.
8. **Use one bounded decision at a time.** Specify what each possible outcome
   would change. Repeating a deterministic prefix, raising memory after an
   unexplained kill, or simultaneously initializing several large catalogs
   is not a substitute for a changed hypothesis. Closeout means stop after
   the outstanding accepted checks and publication, not silently continue
   these proposed experiments.

The public theorem package should contain its literal Lean statements, data,
and checked receipts. Full browser DOM archives are local research evidence,
not theorem dependencies or publication content. Their provenance hashes may
remain in finite audit records without publishing unrelated browser content.

The most concrete future mathematical work is the sixteen-reply N30/N31
response frontier, the original physical P53 state, or the coupled R_gap
exception dispatcher with its newly proved dependencies. Each offers an
exact state and a checkable finite object. None is currently a completed
empty-board strategy.
