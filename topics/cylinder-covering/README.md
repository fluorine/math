# Effective finite cylinder covers of a regular tetrahedron

**[Read the mathematical note (PDF)](output/pdf/cylinder-covering-note.pdf)**
· [LaTeX source](publication/cylinder-covering-note.tex)
· [Full Markdown proof](SECANT-THEOREM.md)
· [Lean proof and reproduction](formal/README.md)
· [Kernel audit](formal/kernel-audit.json)
· [Result and comparison](RESULT.md)
· [Novelty audit](NOVELTY.md)

An explicit family of **20,000 triangular cylinders covers the entire closed
regular tetrahedron** and has certified normalized total base area

$$0.499921585997001674\le R\le0.499921585997001774<0.499922.$$

Here the tetrahedron is exactly

$$K=\{(x,y,\sqrt2s):0\le s\le1,\ |x|\le1-s,\ |y|\le s\},$$

with edge length 2 and minimum orthogonal projection area $A_{\min}=\sqrt2$.
A cylinder extends infinitely along its axis; its base is a compact
nondegenerate triangle perpendicular to that axis. The cost $R$ is the sum
of all base areas, with multiplicity, divided by $A_{\min}$.

The example uses $e=1/10$ and $N=10000$ intervals, with exactly $2N$ cylinders.
In the source's physical convention $\tau=2e$. Its actual maximum axis
tangent is $\sqrt3e(1-1/N)$, measured from its corresponding equality edge.
The proof includes faces, edges, vertices, sector endpoints, zero intercepts
and the interface between the two families.

## What the theorem proves

An exact overlap identity gives the continuous cap

$$C_e(q)=1+e^2(q^2+q^4)/2+9e^4/16.$$

A new perturbation estimate transfers this certificate to the published
compatible secant geometry. Every positive partition has an explicit local
cap buffer and a closed-body coverage proof for $0<e<1$. On equal cells,
for $0<e\le1/10$,

$$|R(e,N)-J(e)|\le\frac{2e}{N},\qquad
N\ge\left\lceil\frac{480}{e}\right\rceil
\Longrightarrow R\le\frac12-\frac{e^2}{240},$$

where $J(e)$ is the continuous cap integral defined in the proof. On the
source count schedule $N=\lceil2/e^2\rceil=\lceil8/\tau^2\rceil$,

$$R\le\frac12-\frac{e^2}{60}+\frac{e^3}{2}+\frac92e^4
=\frac12-\frac{\tau^2}{240}+\frac{\tau^3}{16}+\frac9{32}\tau^4.$$

The bound gives strict saving throughout $0<e\le1/50$. The leading quadratic
coefficient $1/240$ is prior art. The new estimates concern the quartic overlap
padding, its transfer to finite secants, and the resulting effective range and
count/area tradeoff.

## Prior work and comparison scope

The construction builds on the four OpenAI family-100 manuscripts pinned at
revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The secant axes,
shared-boundary first crossing, physical normalization and generic finite
approximation are inherited and credited. The [source guide](sources/README.md)
links the original manuscripts and preserves their license and exact snapshots.

At the 20,000-cylinder benchmark, the new cost is strictly below the proved
actual-area floors for the audited radial and angular constructions on their
**identified explicit sufficient ranges**. The prescribed generic finite
recipes have separate count, area or angle obstructions at that budget.
The [comparison table](RESULT.md#comparison-with-the-published-constructions)
and [source-range derivation](research/published-proof-ranges.md) state the
parameter hypotheses, count conventions and treatment of retuned tilt.

This is not a claim to beat every possible new instance of a generic method,
every possible witness of an existential smallness theorem, or every valid
cover. New admissibility proofs, redesigned cell deletion and different error
allocations can give other constructions. No global optimality is asserted.
Novelty is relative to the documented 15 October 2026 source audit, not an
exhaustive historical-priority guarantee. This is an AI-assisted contribution
shared for public mathematical scrutiny.

## Verification and reproduction

The universal coverage proof is analytical. Independent Python verifiers
reconstruct the polynomial identities, rational error bounds and exact finite
area sums, and separately check the generators' axes, vertices, projections
and physical areas. Exact power sums avoid allocating even the four-million-
cylinder example. No sampled point cloud substitutes for coverage.

The new primary theorem has a [Lean formalization](formal/README.md) of the
actual closed-body coverage, perpendicular triangular bases, geometric area
sum, exact angle, finite error estimates, count schedules, two-sided asymptotic
remainder, arbitrary-partition mesh bound and complete numerical interval.
The public theorem `TetrahedronCover.tetrahedron_20000` combines the actual
20,000-cylinder coverage and area claims in one statement. The
[kernel audit](formal/kernel-audit.json) records the final checked statements,
axioms, build and standalone replay; negative controls are included.

The analytical PDF and LaTeX are preserved as published. Their verification-status
paragraph predates this Lean addendum and is superseded by the current audit.
The historical source-comparison and restricted-class optimality arguments remain
separately identified written proofs with exact-arithmetic checks. No human
referee review is claimed.

From a clean checkout, Python 3.9 or later and its standard library suffice:

```sh
git clone https://github.com/shjvandekamp/math.git
cd math
python3 topics/cylinder-covering/reproduce.py
```

This checks all 91 source hashes and available Git blob IDs, runs both exact
verifiers serially, and requires their output to match the recorded certificates.
This Python-only command needs no network, external Python packages, computer
algebra system or Lean. To run the complete formal audit after installing the
pinned Lean/mathlib dependencies as described in [formal/README.md](formal/README.md):

```sh
python3 topics/cylinder-covering/reproduce.py --formal --fresh
```

The command recompiles every local proof module, checks the final axiom lists,
replays each local module through Lean’s kernel replay implementation, and
requires rejection of two deliberately false proof obligations.

Generate any one cylinder, with exact rational data, by index:

```sh
python3 topics/cylinder-covering/secant_construction.py --epsilon 1/10 --n 10000 --index 0
```

The output uses coordinates $(x,y,z/\sqrt2)$ with metric
$\operatorname{diag}(1,1,2)$, and includes the perpendicular base vertices,
axis and exact area expression. No large cylinder list is required.

To rebuild the PDF with Tectonic:

```sh
tectonic --outdir topics/cylinder-covering/output/pdf topics/cylinder-covering/publication/cylinder-covering-note.tex
```

## Complete supporting material

- [Primary secant proof and inequality dependencies](SECANT-THEOREM.md).
- [Radial proof, sharp constant quartic padding and finite enclosure optimality](THEOREM.md).
- [Independent secant verification](verification/secant-report.md) and [recorded output](verification/secant-last-run.txt).
- [Independent radial and comparison verification](verification/REPORT.md) and [recorded output](verification/last-run.txt).
- [Arbitrary radial partitions and angular comparisons](research/published-radial-angular-comparison.md).
- [Published proof ranges and count conventions](research/published-proof-ranges.md).
- [Generic grid, product/log, nilpotent and beam comparisons](verification/published-generic-comparison.md).
- [Slope-field comparison](research/published-slope-comparison.md).
- [Sharp finite triangle and partition optimum in its declared class](research/finite-triangle-optimality.md).
- [Source inventory and hashes](sources/manifest.json), [novelty record](NOVELTY.md) and [research state](STATE.md).

The earlier radial realization remains reproducible through `construction.py`.
Its exact full-sweep enclosure class has a sharp leading finite loss $4e/N$;
the preferred compatible secants lie outside that enclosure constraint.
