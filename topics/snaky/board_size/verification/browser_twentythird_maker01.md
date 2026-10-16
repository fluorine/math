# Finite R_gap continuation claims from Browser01 round23

Publication reproduction: from `board_size/`, run
`python3.12 -B reproduce.py browser_twentythird_maker01 --output /tmp/browser_twentythird_maker01-publication.json`.
The historical receipt below is preserved. The wrapper records a separate
replay using sanitized mathematical text; see [the reproduction guide](../reproduction/README.md).


The independent finite audit passed once. No solver or game search was used.
The report is `browser_twentythird_maker01.json`, SHA256
`1784cec870052b95f5a3904e17d3b6581db2cc419b00e40c69f48a363bad92e4`.
The accepted starting point is the exact 27+27
R_gap+M(6,3)/B(5,3) state and its63 pairs, protecting370 of385 live full
Snakies. The accepted five-round history ends at32+32 with57 pairs and12
exceptions. Every old color is retained.

The new checker independently regenerates all1,040 literal targets and
reconstructs the accepted pair family, full15-exception inventory and exact
five-round switch. Its new claims are deliberately separate:

1. At the accepted32+32 state, M(10,12) forces B(9,12) through full T14.
   At the resulting33+33 state, five members of the original370-target
   protected family have fresh requirements `bf`, `abc`, `bcde`, `dfgh`,
   `cdgi`, with the nine actual cells specified in the report. A disjoint
   matching must successively contain `bf`, `ac`, `de`, `gh`, leaving only
   `i` available in the last target. This excludes arbitrary fresh global
   matchings, not adaptive physical defenses. Five displayed deletion
   matchings check inclusion-minimality. A nine-entry local response table
   confirms that even this selected five-target game has an adaptive defense;
   that table is not asserted to compose with the remaining physical board.
2. The opposite T14 choice, M(9,12)/B(10,12), preserves the original370-target
   family with55 fresh pairs. The checker enumerates all four full exposures
   of retired P63 and the exact nine remaining exceptions. It is a partial
   preservation result, not a complete matching leaf.
3. From the original27+27 state, the six stated mate rounds ending in
   M(4,13)/B(5,13) allow M(3,10) to fork the actual completions(2,14) and
   (4,14). Every legal physical Breaker response is checked against a full
   Snaky and the final Maker claim. The prefix contains no earlier one-cell
   exceptional threat. Thus this refutes the policy class that follows the
   original mates until an unmatched entry or such a threat; it does not
   force those six Breaker choices against unrestricted play.
4. Just before the sixth reply, only (3,10),(2,14),(4,14) prevent that fork.
   For every other fresh reply the checker enumerates the following physical
   responses and terminal claims. Each of the three interventions leaves the
   full protected target E_L with requirement
   `{(3,12),(5,13),(6,13),(7,13)}`. Retaining all P50,P60,P61 leaves just
   (5,13) available for a new pair, so at least one must be released if a
   fresh-matching invariant for the old protected family is restored.

The sole run used4 internal CPU /20 internal wall seconds under the
unchanged5 CPU /30 wall /100 MiB guard, nice19 and one native thread.
Eleven rejection controls passed, testing lost old colors, changed or occupied
obstruction requirements, overlapping pairs, self-replies, wrong forcing
targets and missing or blocked physical fork witnesses. Each T14 branch
checks131 legal replies, with130 immediate losing deviations. The earlier
T15 branch checks133 replies. The left fork checks129 actual final replies;
the128 excluded pending-sixth replies give16,512 further terminal branches.
All five deletion matchings and all nine selected-game rows passed.

Child66287 exited0 after0.2638 process CPU seconds and0.4328 guarded wall
seconds. The process-family peak was57,688,064 bytes, with no pressure events.
The conservative35% two-sample gate and direct stable-swap check passed.
No retry was used. Source SHA256:
`72349c6214d77cffc66a7aaf5a7972117f207a3b25b2a9a163287a903d3fe537`.
The exact command, interpreter, source/input pins, preflight and logs are
bound by `browser-twentythird-maker01-01.execution01.json` and its launch record.

Underlying reproduction command, using a fresh output path:

```
python3.12 -B reproduce.py browser_twentythird_maker01 --output /tmp/browser_twentythird_maker01-publication.json
  --output verification/browser_twentythird_maker01.json
```

The stopped unrestricted T14 solver adapters remain unrun. This finite
argument may rule out one of their static questions without executing it;
it does not settle either empty-board objective or the R_gap parent.
