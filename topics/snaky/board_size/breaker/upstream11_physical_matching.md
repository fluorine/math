# Static physical defense one turn before M31

Publication scope: this is a curated research note. Large search decks,
solver logs, and unrun adapters named in the historical text remain outside
this compact package. Included finite receipts and the Lean theorem sources
are distinguished in [the closeout guide](../README.md).


Independently verified: **32 disjoint free pairs defend S11**. The unchanged
full physical checker accepted all432 Snaky placements, including all144
targets still live at this state. The ordinary certificate is
`verification/upstream11-physical-matching-result-01.pairing.json`.

Report `verification/upstream11-physical-matching-result-01.json` has SHA256
`6ec266d1c68e26e96f4ca292e8177d1ebb5494f9599089e944e5ad5168c08cb0`.
The adjacent execution record binds the reviewed sources, exact formula,
complete model, certificate and each separate resource guard.

The exact position has11 Maker and11 Breaker stones, with Maker to move:

- Maker:11,21,37,44,45,46,47,57,67,75,84.
- Breaker:14,34,36,38,43,55,56,58,74,77,94.

It follows the complete physical prefix M11/B14,M21/B43 from the accepted
9+9 colors. Equivalently, undo only M31 and B41 from the independently
accepted postM31 pairing leaf. No other color is removed or reinterpreted.
The new problem has78 free cells and includes all432 literal Snakies.

A repository search for S11, upstream11, postM21, the11+11 labels and the
actual prefix found no earlier unrestricted static query at this state.
Existing D13/D14 local checks reserve component domains or exterior pairs;
they are different problems. The accepted static and first-entry
obstructions at S9 are preserved and are not being queried again.

The constructor calls unchanged `static_pairing.encode` on every full live
target after deleting only physically Maker-owned cells. Every co-occurring
free pair is eligible. Per-cell at-most-one constraints enforce disjointness,
and each live target must contain a chosen pair. The old35-pair certificate
is used only to list newly uncovered targets. No old pair is fixed, and no
cell, response or target is projected away. Any singleton residual gives an
empty coverage disjunction; it is not silently dropped.

The independent verifier imports no constructor. It replays the literal
prefix, regenerates all432 Snakies with the existing independent geometry,
rechecks the accepted successor certificate, and reconstructs every SMT
declaration and clause. The focused controls reject wrong colors, incorrect
undo operations, fixed pairs, clipped cells, omitted targets/capacities,
partial Boolean models and a false SAT cover. Two additional controls keep
cutoffs UNKNOWN and unproved UNSAT restricted to the static class.

The reviewed execution used one5 CPU/30 wall/100 MiB export, one10 CPU/60 wall/
150 MiB independent encoding audit with the12 controls, then one30 process
CPU/120 guard wall/200 MiB Z3 query at150 MB solver memory, one thread,
seed0 and nice19. The unchanged same-PID CPU launcher and pressure guard
apply. The final independent result acceptance has10 CPU/60 wall/150 MiB.
The actual formula and encoding-audit hashes were pinned before the solver.
One preflight held before any child because direct swap usage had grown.
After fresh stable samples, all four phases completed normally without
pressure events. The12 controls passed once. The sole solver ran for0.214
guarded seconds; the separate acceptance used0.04216 CPU seconds. No query
was repeated and no memory limit was increased.

The complete SAT model declared every Boolean exactly once and passed the
unchanged full physical pairing checker before the standard certificate
was emitted. Whenever Maker enters a pair, Breaker claims its fresh mate;
if the mate is already Breaker's, or Maker enters an unpaired cell, a legal
filler preserves the defense. Every live Snaky contains a protected pair,
so this includes immediate and final-claim wins.

This result defends the conditional S11 Maker-turn state. It does not
quantify over the earlier choices or prove an S9 or empty10 result.

Recheck the saved model and physical certificate without solving again,
from `topics/snaky/board_size`, using a fresh output path:

```sh
python3.12 -B verification/check_upstream11_physical_matching.py \
  --input breaker/experiments/upstream11-physical-matching-01.json \
  --input-sha256 5bbd8781ee8ab27ea90ee52cba3319780db45138decb8af63fa1840c868028a8 \
  --formula breaker/experiments/upstream11-physical-matching-01.smt2 \
  --guard breaker/experiments/upstream11-physical-matching-solver-01.guard01.json \
  --guard-sha256 d02baf1e06c40d72fa3ea9da435dcb4cb514da29f92688ee6f0ab473f925056b \
  --output /tmp/upstream11-physical-matching-recheck.json
```

The postM31 source, report, formula and accepted certificate remain frozen.
