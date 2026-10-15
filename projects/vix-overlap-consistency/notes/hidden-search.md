# Hidden-schedule constructive search

Date: 2026-10-15. Contract: [EXTENSION.md](../EXTENSION.md). The latent-data
certificate described here is now kernel-checked in Lean. The full filtered
market construction was a separate integration obligation, now completed as
recorded in the final section below. No broader infeasibility claim is made.
The existing early-revealed theorem is unchanged.

## Result

The first feasibility solve found a joint law of the six activity bits and
three fixing signals with **39 positive states and denominator 1024**.
The complete exact table is [hidden-witness.json](../certificates/hidden-witness.json).
Every prescribed prefix-count marginal, signal marginal, and conditional-history
equation passes rational arithmetic checks. There were no failed search
attempts, no rounded equality constraints, and no solver-grid enlargement.
This establishes a concrete candidate for the hidden-information construction;
the market-model, quote, mixture, and Lean proof obligations remain separate.

## Search class and exact rows

Initially include every pair `(a,y)` in `{0,1}^6 × {0,1,2,3}^3`: 4096 states.
Both tuples use lexicographic order. A schedule's first bit is its most
significant binary digit; a signal triple's first entry is its most significant
base-four digit. Write

`Wi(a) = a[i+1] + a[i+2] + a[i+3]`, for zero-based `i=0,1,2`.

The search variables are their joint masses `p(a,y)≥0`. Independent fair
return signs will be added by the filtered-model construction; they are not
variables in this LP. At fixing `i`, its activity/signal history is

`(a[:i+1], y[:i+1])`.

The rational system has 624 equality rows:

- 28 prefix atoms: for every `j=0,…,6` and `k=0,…,j`, the mass with
  `sum(a[:j])=k` is `choose(j,k)/2^j`. The `j=0` row gives normalization.
- 12 signal atoms: the four masses of each signal have numerator rows
  `(12,12,36,4)`, `(2,30,30,2)`, and `(1,46,1,16)`, each over 64.
- 584 full-history rows: at every fixing and every possible history key,
  `sum_history p(a,y) * (Wi(a)−yi) = 0`. There are `8+64+512` keys.
  All keys are retained, including those with zero mass or no supported states.

The last equations are unnormalized. No history probability is divided out,
and zero-probability histories impose only `0=0`. Because past fair signs are
independent of the schedule and signals, conditioning additionally on any fixed
past sign vector multiplies these equations by the same positive factor.
That observation is a construction route, not a substitute for its Lean proof.

## Sound support pruning

The LP removes states for which `yi=0` but `Wi(a)≠0`, or `yi=3` but
`Wi(a)≠3`. This leaves 748 states.

For a history with `yi=0`, each term `p Wi` is nonnegative. A zero sum forces
every positive-weight state's count to be zero. For a history with `yi=3`,
each term `p (3−Wi)` is nonnegative and the same reasoning applies. Thus this
pruning follows from the full history equations and nonnegativity; it does
not select an arbitrary numerical grid. Any law on the remaining states
extends to all original states by assigning zero to the removed states.

## Exact verification and reproducibility

Discovery and checking are implemented in
[discover_hidden.py](../scripts/discover_hidden.py). From the project directory:

```sh
nice -n 19 .venv/bin/python scripts/discover_hidden.py
nice -n 19 python3 scripts/discover_hidden.py --check certificates/hidden-witness.json --check-lean
```

The discovery call uses SciPy 1.13.1's HiGHS dual-simplex feasibility solve
with zero objective. It restricts BLAS/OpenMP-related thread counts to one.
The initial solve returned success in approximately 0.018 seconds. The
whole command took 1.57 seconds, with a measured peak memory footprint of
44,368,896 bytes. Only one solver process ran.

Floating-point masses are used only to propose rational values through
`Fraction.limit_denominator`. A candidate is saved only after every original
row has zero exact `fractions.Fraction` residual, the weights are nonnegative,
and the total mass is exactly one. The history equations receive a second
check directly from the sparse support and the original history definitions,
independently of the LP coefficient matrix. The saved certificate contains
integer numerators and a common denominator; no floating-point equality is
part of the proposed mathematical data.

The saved-certificate check uses only the Python standard library. Its
`--check-lean` option also compares all three 39-entry literal vectors and the
denominator with `HiddenData.lean`; the numerical search libraries are loaded
only when running a new search.

The 39 listed numerators sum to 1024. Appending all 64 independent fair sign
vectors gives 2496 positive raw states, each with mass `numerator/65536`.
Using all original schedule/signal/sign tuples instead gives the identical
law on 262144 labeled states, with zero weights elsewhere. The broad class
permits either finite representation; no support-minimality claim is made.

## Lean certificate and remaining integration obligations

The following new modules compiled successfully with the pinned Lean toolchain:

- [HiddenData.lean](../formal/VixOverlap/HiddenData.lean) defines the positive
  carrier `Hidden.Atom = Fin 39`, its schedules, signals, exact weights, and
  latent history equivalence relation. The history and refinement lemmas
  enforce precisely the declared revelation times.
- [HiddenCertificate.lean](../formal/VixOverlap/HiddenCertificate.lean) proves
  strict positivity, total mass one, all prefix and signal atoms, all six
  activity means equal to one half, and every fixing/history conditional
  equation. Ordinary kernel `decide` checks the finite integer identities;
  proved cast-and-division lemmas transfer them to real weights. It also
  constructs `Hidden.law` and `Hidden.latentFiltration`.

`#print axioms VixOverlap.Hidden.certificate` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The data and certificate compiles exited
with status 0; the certificate check took 25.29 seconds with measured peak
memory footprint 138,556,480 bytes. No native computation oracle is used.
The exact JSON-to-Lean check also passes. These statements certify the latent
data; they do not assume or assert the existence of the full financial model.

Before calling the extension complete, formalize the finite conditional
budgets, the refinement filtration with signals arriving only at their
fixings, all full-history martingale/diagonal/tower rows, the unchanged
ordinary-call panel, root budgets, and the common moment envelope. The
checked certificate must be connected to those structural and quote rows.

This search treats only `ε=0`. Coverage of the full unchanged target family
requires a separately proved mixture construction, including the information
revealed about the mixture component. A convex mixture of marginal tables
alone does not establish the required filtered identities.

## Completed integration

On 2026-10-15, the complete verifier rebuilt all 27 local modules with exit
status 0. `Extension.financial_same_panel_compatibility` now proves the full
financial construction and exact ordinary panel for every real `0≤ε≤1`.
The earlier remaining-obligation paragraphs record the discovery checkpoint;
all of those obligations are now discharged by HiddenModel, HiddenQuotes,
Mixture and ExtensionHeadline. The 39 distinct audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. See
[extension-verification.log](extension-verification.log) and
[VERIFICATION.md](../VERIFICATION.md). No continuous realization is claimed.
