# Physical M43 reduction and two matching questions

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentyfirst_independent05 --output /tmp/browser_twentyfirst_independent05-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed. At the exact physical S9 position, M43
rules out 79 of 81 Breaker replies under the displayed physical winning tree.
Only B52 and B53 survive this proof. At the time of this audit, their resulting
11+11 states remained open. At closeout, [original P52 is defended in Lean](../../formal/Snaky/P52.lean);
original P53 remains open. The matching observations below are historical.

At the exact physical S9 position, Maker owns
`37,44,45,46,47,57,67,75,84` and Breaker owns
`34,36,38,55,56,58,74,77,94`. All coordinates are zero-based `10*y+x` cells on
the 10×10 board. The checked first move is M43.

The checker enumerates all 81 fresh Breaker replies. For the 78 replies outside
`{52,53,54}`, it checks M53 and every next physical reply before the final
M52/M54 completion. For B54 it checks every deviation from M32/B33 and
M42/B31, then every reply to M52's fork at51/53. For B52 and B53 it checks every
reply to M32; only B33 remains. Five distinct full Snakies certify the terminal
claims. No target is projected, and every old color remains present.

The two remaining states are:

- Maker `32,37,43,44,45,46,47,57,67,75,84`; Breaker
  `33,34,36,38,52,55,56,58,74,77,94`, Maker to move.
- The same Maker set; Breaker
  `33,34,36,38,53,55,56,58,74,77,94`, Maker to move.

The accepted S11 matching is only an inventory aid here. The checker reloads
its 32 pairs and independently verifies that original S11 leaf. It then
rechecks the accepted 18-gap S9 inventory using all 432 full targets. In each
new state it retains only fresh pairs, leaving 29 pairs. It compares
the entire live uncovered family with the browser's exact 13- and 16-target
lists, including all damaged-pair incidences. These partial matchings do not
certify either state.

The checker is `../verification/browser_twentyfirst_independent05.py`. The
single audit used 4 internal/5 outer CPU seconds, 25 internal/30 guarded wall
seconds, 100 MiB, nice19, one thread and the unchanged resource guard. Seven
rejection controls and one positive final-claim control passed. It checked
6,547 terminal branches plus two unresolved exact frontiers; the report retains
every first-reply classification, full physical witness and complete 432-target
inventory at each frontier. General interleaving, neutral-entry dispatcher and
the browser's further mandatory-pair chain are outside this audit.

The two approved unrestricted full-physical static-matching queries are now
complete. Each used the frozen `static_pairing.encode`, all 432 targets, all
old occupancy and every possible fresh pair. None of the old 29 or proposed
replacement pairs was fixed. Both returned UNSAT normally. The independent
audits checked the exact formulas and result classification; no UNSAT proof
was generated or accepted, so neither physical game is resolved by this result.

| First reply | Live targets | Pair variables | Solver PID | Guarded wall | Peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| B52 | 146 | 630 | 50410 | 0.2121 s | 24,936,448 bytes |
| B53 | 155 | 636 | 50602 | 0.2122 s | 24,920,064 bytes |

Both used one nice19 thread, seed0, 30 process CPU seconds, 120 guarded wall
seconds, 200 MiB sampled RSS and 150 MB Z3. Every phase passed a fresh aggregate
resource gate at the new stable swapout total 18,725,518. There were no pressure
events or retries. The solver reported 0.01 seconds total time in each run;
separate completed process CPU measurements were not recorded.

Repository inspection found no dedicated saved Z3 static query at these exact
states before these queries. The earlier depth3 in-process S9 experiment may have visited them but
did not preserve per-state negative oracle histories; no accepted positive at
either state was identified. The completed 78-question batch queried the
earlier 10M/9B states, so it does not duplicate either 11+11 question.

The finite report is `../verification/browser_twentyfirst_independent05.json`,
SHA256 `56d03252b70a863dd35137507b7e594e0d62af0f05854365a814aa73ab5ef45b`.
It used 0.0618 CPU seconds, 0.2119 guarded wall seconds and 24,133,632 bytes peak
RSS, with no pressure events. The frontiers have 146 and 155 live physical
targets respectively. The guard, launch, preflight and execution receipts
share the report's stem. Reproduction from `board_size`, into a fresh file:

```sh
python3.12 -B reproduce.py browser_twentyfirst_independent05 \
  --output /tmp/browser-twentyfirst-physical-replay.json
```

The reviewed matching source package is:
`twentyfirst_physical_matching.py` exports one selected branch, and
`../verification/check_twentyfirst_physical_matching.py` independently binds
both complete physical states, reconstructs every clause, and checks every
positive against all 432 targets. Its first encoding audit passed 11 focused
controls, including old-color loss, omitted coverage/capacity, forbidden fixed
pairs, partial models, signal cutoffs and unchecked UNSAT scope. The controls
ran once and were not repeated for the second branch.

The immutable source-only execution proposal is
`experiments/twentyfirst-frontier-matching-01.plan.json`, SHA256
`274a1e65689eda84e8b3eb17cf07fb1d429b307a438915db85d15557940b868c`.
It remains unchanged as the pre-execution record. The completed receipt is
`experiments/twentyfirst-frontier-matching-01.receipt.json`, SHA256
`83b588a0f9b3f55e742c7ea28eede90ba4501367a2435f3004b38f7e3912ebe9`.
It binds every exported instance, exact formula, encoding audit, direct solver
command, binary/version, preflight, log, resource guard and result audit.

The independent result files are
`../verification/twentyfirst-frontier-b52-result-01.json`, SHA256
`954b17442c991834dab58b67fb8156eb58035cab3d158efd417260408d5cf7cc`, and
`../verification/twentyfirst-frontier-b53-result-01.json`, SHA256
`ffa0ba6ab3b0d5cca47f809aa37eedf0cd8332dbafb03e648375813c05e901ae`.
Their status is `unproved_static_matching_unsat_observation`. Reproduce the
independent binding/classification using each saved result-audit launch argv
with a fresh `--output` path; this replays the immutable solver output without
another solve in the local historical snapshot. This was the status before
the later P52 defense; original P53 remains open for adaptive defense or
physical Maker analysis.
