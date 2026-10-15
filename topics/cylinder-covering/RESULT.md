# Result: an effective quartic/secant cover of the regular tetrahedron

A new quantitative coverage theorem and an independent exact certificate are
complete. For the fixed tetrahedron with A_min=sqrt(2), the preferred
construction uses **20000 compact nondegenerate triangular perpendicular bases**
and has normalized total area

$$
\boxed{0.499921585997001674\le R\le0.499921585997001774<0.499922.}
$$

The physical parameter is tau=1/5 (canonical e=1/10), and its actual maximum
axis tangent is exactly sqrt(3)*(1/10)*(9999/10000). The proof covers the
entire closed body, including faces, edges, vertices, sector endpoints,
zero intercepts and the middle interface. The interval is outward-rounded
rational arithmetic, not a numerical coverage experiment.

The publication note is available as [PDF](output/pdf/cylinder-covering-note.pdf)
and [LaTeX](publication/cylinder-covering-note.tex). The full Markdown manuscript
is [SECANT-THEOREM.md](SECANT-THEOREM.md), with the
independent derivation and checks in [secant-report.md](verification/secant-report.md).

## What creates the gain

Exact elimination of the two intercept equations yields a nonnegative square
certificate for the continuous cap

$$
C_e(q)=1+e^2(q^2+q^4)/2+(9/16)e^4.
$$

It replaces the source radial criterion's cubic padding by quartic padding.
The coefficient 9/16 is sharp among constant quartic corrections, with actual
uncovered boundary points for smaller constants at sufficiently small e.
This is a specified cap-class optimum, not global optimality of covers.

For the finite realization, compatible secant sectors preserve shared sides.
A new explicit perturbation bound transfers the quartic certificate to the
discrete axes. Its cap buffer is ed/2+O(e^2d+e^2d^2), where d is cell width.
Every base is the perpendicular projection of an explicit intercept triangle.

For 0<e<=1/10, the theorem provides exactly 2N cylinders and

$$
|R(e,N)-J(e)|\le2e/N,
\qquad
N\ge\lceil480/e\rceil\ \Longrightarrow\ R\le1/2-e^2/240.
$$

On precisely the source count schedule N=ceil(2/e^2)=ceil(8/tau^2),

$$
R\le\frac12-\frac{e^2}{60}+\frac12e^3+\frac92e^4
 =\frac12-\frac{\tau^2}{240}+\frac{\tau^3}{16}
     +\frac9{32}\tau^4.
$$

Strict saving is proved throughout 0<e<=1/50, with margin at least
(73/15000)e^2. The actual cubic coefficient of this specified construction
is 1/2. The leading quadratic coefficient 1/240, secant geometry,
first-crossing argument and generic finite approximation are prior art.
The new contribution is the quartic overlap estimate and its effective
finite admissibility/count range. [NOVELTY.md](NOVELTY.md) records the audit
and separates source corollaries from new estimates.

## Comparison with the published constructions

The comparison uses the identified published sufficient ranges and count conventions.
At at most 20000 cylinders and at most the new actual axis tilt, the audited
source recipes have the following obstructions. The radial and generic bounds
allow the slightly larger tangent budget sqrt(3)/10 as well.

| Source recipe on its identified explicit sufficient range | Proved comparison |
|---|---|
| Radial linear, cubic, fractional and square-root caps; arbitrary tags/partitions and actual projected bases | Actual R>=1/2-1/23328000>0.49999995, even with retuned source tilt |
| Quantitative angular maximum caps, optimized old mesh budget, and cubic-buffer family | Actual R>=1/2-1/93312000 |
| General compatible angular construction, including its ordinary, squared, Cartesian and table specializations | Actual R>=1/2-1/5529600000; full count>=36864000 |
| Separate direct endpoint and squared constructions | At least 392000002 and 800000000 cylinders respectively |
| Alternative Cartesian local certificate | Actual R>0.499999999996 for any resulting complete cover |
| Rational/singular full retained-grid realization | Actual R>=637/1250>1/2 at this budget |
| Rational product/logarithmic realization with published saving-error allocation | Over 20 million selected main cylinders in one family, even after finite-subcover selection |
| Nilpotent construction's prescribed apex lists | More than 34133 cylinders before its interior cover |
| Shortened beams plus the prescribed strip | A required strip axis exceeds arctan(1/3), outside the tilt budget |

These are actual-area, count or angle bounds, not comparisons against selected
loose source upper bounds. The old angular argument can itself be optimized:
its printed budget gives cubic coefficient 16 in e units, retaining the actual
source-schedule mesh improves it to 29/2, and arbitrarily finer meshes give 14.
Those corollaries are included, rather than treating Proposition 6.1's
coefficient 100 as the entire frontier.

The precise source ranges, including the explicit witnesses extracted from
the Lean proofs, are in [published-proof-ranges.md](research/published-proof-ranges.md).
The geometric proofs are in [the radial/angular note](research/published-radial-angular-comparison.md)
and [the generic comparison](verification/published-generic-comparison.md).
[The slope-field note](research/published-slope-comparison.md) separately
records fixed-parameter continuum coefficient comparisons.

These conclusions concern the published recipes on their identified numerical
sufficient ranges and prescribed finite realizations. They do not assert that
every possible witness of an existential smallness theorem satisfies the
published numerical witness. Larger valid ranges, redesigned cell deletion,
new error allocations, and arbitrary new instances of generic methods are
outside the benchmark. Fixed-positive-margin source families also admit a
same-count, exactly matched finite-angle comparison for sufficiently small
admissible tilt, with explicit thresholds in their constants. No global
optimality or exhaustive novelty guarantee is claimed.

The formerly conditional eta=1/1000,tau=1/5 angular example now has a full
coverage proof from the new certificate. Its curved-base area is <0.499937;
its triangular enlargement is <0.499940. This extends its known feasibility
range. It is not a cover certified at that tilt by the old source thresholds.
The preferred new maximum-cap triangles have smaller caps on every cell.

## Additional sharp finite-budget result

The earlier radial realization remains in [THEOREM.md](THEOREM.md) and
[construction.py](construction.py). Its 20000-cylinder cost was
[0.499947504745824,0.499947504745984]. Its triangle is uniquely optimal among
all triangles of the declared symmetric form enclosing the entire constant-cap
frozen sweep. Optimizing over every N-cell midpoint partition cannot remove
the leading finite loss 4e/N. On N=ceil(2/e^2), the best cost in that full-sweep
enclosure class is 1/2-e^2/60+2e^3+O(e^4).

This class-wide lower bound explains the change to compatible secants, which
need not enclose every continuously tilted sweep in each cell. It does not
assert optimality for curved bases, asymmetric triangles or all tetrahedron
covers. The old e=1/100,N=20000 radial example failed to save area; the new
secant construction at that same count has certified ratio
[0.499998863418315727,0.499998863418315728].

## Reproduction and publication

From the repository root:

```sh
python3 topics/cylinder-covering/reproduce.py
python3 topics/cylinder-covering/secant_construction.py --epsilon 1/10 --n 10000 --index 0
```

Only standard-library Python is required. The verifiers reconstruct the critical
identities and use exact power sums, so even the four-million-cylinder example
allocates no cylinder list. Generator checks separately verify both families,
physical metric, projections, vertices and area. Saved outputs are in
[verification/last-run.txt](verification/last-run.txt) and
[verification/secant-last-run.txt](verification/secant-last-run.txt).

All 91 source snapshots are pinned in [sources/manifest.json](sources/manifest.json).
The complete package is published under
[`topics/cylinder-covering`](https://github.com/shjvandekamp/math/tree/main/topics/cylinder-covering).
It includes the PDF, standalone LaTeX, full supporting derivations, generators,
independent exact certificates and source attribution. The research used
standard-library exact arithmetic without cloud compute or large cylinder arrays.
The primary theorem is now formalized in Lean; see the [formal proof guide](formal/README.md)
and [kernel audit](formal/kernel-audit.json). This covers the actual geometric
construction and its full quantitative claims. The comparison with earlier
constructions and supplementary restricted-class optimality remain separately
identified written arguments. The preserved analytical PDF predates the Lean
addendum. No human referee review is claimed.
