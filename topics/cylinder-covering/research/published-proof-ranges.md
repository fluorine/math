# Published proof ranges and the finite comparison

This note compares the published constructions on their identified explicit
sufficient parameter ranges and stated count conventions. All source paths below are
relative to `sources/lean/OAI/Geometry/CylinderCovering/`, pinned to revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Source proofs are inspected as
mathematical text; no local Lean compilation is claimed. The geometric and
area lower bounds are proved in the companion comparison notes.

The earlier manuscript-only assessment left an apparent gap because several
theorem statements say “sufficiently small.” The source Lean proofs give
explicit witnesses. Those witnesses close the comparison on the identified explicit published
sufficient ranges. This does not assert that every possible witness of an
existential theorem must satisfy these particular numerical thresholds.
Larger valid ranges are not declared impossible; establishing
one can itself be a new feasibility result, as SECANT-THEOREM.md demonstrates.

## 1. General compatible angular data

`Angular/GeneralDefinitions.lean` defines `Admissible tau eta E D` and the
exact integral cost. `Angular/GeneralCoverage.lean`, theorem
`covers_of_admissible`, and `Angular/GeneralAssembly.lean`, theorem
`coordinate_cover`, use

$$
E\ge0,\quad 0<\eta\le1/480,\quad 0<\tau\le1/2,
\qquad (10+4E)\tau\le\eta.                         \tag{P1}
$$

`Angular/GeneralVolume.lean`, `totalArea_div_H_eq_integralCost`, identifies
actual perpendicular area divided by H with that integral. Theorem
`integralCost_expansion` in `Angular/GeneralAssembly.lean` proves

$$
\left|R-\left(\frac12+(2\eta-1/240)\tau^2\right)\right|
\le(6E+2)\tau^4,                                    \tag{P2}
$$

assuming eta<=1/8, tau^2<=1 and E*tau^2<=1/16. These follow from (P1).
The smallness witness in `Convexity/GeneralCapArea.lean`,
`exists_uniform_smallness`, explicitly includes eta/(10+4E).

Since E*tau<=eta/4 and 10*tau<=eta, the remainder in (P2) is at most
(17/10)*eta*tau^3 <= (17/20)*eta*tau^2. Consequently

$$
R\ge\frac12-\frac{\tau^2}{240}
\ge\frac12-\frac1{5\,529\,600\,000}
>0.499999999819.                                    \tag{P3}
$$

There is also a count obstruction. On a cell [l,r], admissibility requires
the constant beta to approximate q/2 with error at most E*tau^2 at both
endpoints. Thus r-l<=4E*tau^2. For m positive cells covering [-1,1],
m>=1/(2E*tau^2). Positive cells force E>0. Optimizing the quadratic

$$
E\tau^2\le\frac{\eta\tau}{4}-\frac52\tau^2
\le\frac{\eta^2}{160}
$$

gives the full two-family count

$$
2m\ge\frac{160}{\eta^2}\ge36\,864\,000.              \tag{P4}
$$

This counts the prescribed source cells; it does not count a redesigned
subcover that deletes cells using an additional coverage argument. The area
bound (P3) is independent of the number of prescribed cells.

| Published route | Explicit certificate used |
|---|---|
| Ordinary secant continuous, maximum, and radial caps | `Angular/OrdinaryCaps.lean`, `Angular/OrdinaryCover.lean`: general admissibility with E=M and mesh<=M*tau^2 |
| Squared caps through the general theorem | `Convexity/SquaredCapCover.lean`: E=max(M,(1/8+eta)^2), then (P1) |
| Cartesian caps | `Cartesian/Cover.lean`, `CoverEligibility.lean`: E=max(M,12), (P1), and tau<=1/4 |
| Table/node construction | `Angular/TableCover.lean`: E=32, mesh<=32*tau^2, (P1), tau<=1/4 |
| Endpoint construction, separate direct certificate | `Angular/EndpointCover.lean`: k>=14000, exactly 2(k^2+1)>=392000002 cylinders |
| Standalone squared direct construction | `Angular/SquaredDirect.lean`: 0<k<=1/20000, full mesh width 2k^2, hence at least 800000000 cylinders |

The two direct certificates in the last rows are handled separately; they
are not silently assigned the general theorem's range. The squared direct
count follows by summing cell lengths over an interval of length 2, and
does not rely on 1/k^2 being an integer. A final shortened cell cannot lower
the count. An alternative local Cartesian certificate can be bounded separately:
`Angular/CartesianRemainder.lean`, `cartesian_root_sum_gt_one`, assumes
256*tau*(2+eta)<=eta. With eta<=1/480 this forces tau<=1/246016.
Its cap retains radial extent at least 1/2, and its secant directions obey
alpha^2+2beta^2<=3/4. Thus any complete realization using this certificate
has R>=(1/2)/sqrt(1+3tau^2/4)>=1/2-3/(16*246016^2)>0.499999999996.
This does not assert a separate assembled complete-cover theorem.

## 2. Radial cap families

The source's common overlap criterion for a cap 1+e^2(h+b) is
b(p)+b(q)>=9e. The following published proof ranges satisfy it, either
directly or by inclusion of a smaller cap.

| Source cap and location | Published sufficient range and implication |
|---|---|
| Linear, `Radial/CapCoverage.lean` | 0<e<=2*beta/9, so 2b=2beta>=9e |
| Cubic, same module | c>=9/2, so b=ce and 2b>=9e |
| Fractional, same module | c>0, e<=(2c/9)^2, so b=c*sqrt(e)>=9e/2 |
| Square-root, `Radial/SqrtCap.lean`, `SqrtRealization.lean` | 0<e<min(1,beta/9,beta/(1+beta)^2); the cap contains the linear cap with b=beta/2, and beta>=9e |
| Half-height cubic, `Caps/Caps.lean` | delta>0, e=delta/2, b=32delta>=9e/2 |
| Half-height fractional, same module | 0<delta<=1, e=delta/2, b=8sqrt(delta)>=9e/2 |

The exact rescaling dictionaries are in `Radial/CapVariants.lean` and the
pinned definitions modules. Therefore the actual-area bound from
`published-radial-angular-comparison.md`, including arbitrary partitions,
tags and retuned tilt, applies throughout these proof ranges:

$$
R_{\rm radial}\ge\frac12-\frac1{23\,328\,000}>0.49999995,
\tag{P5}
$$

provided every finite axis is within arctan(sqrt(3)/10) of its assigned
equality edge. Actual projected bases are included, as are larger published
triangles, trapezoids, and polygons. No maximality of a sufficient range is
asserted.

## 3. Optimize the old angular sufficient condition too

Proposition 6.1's cubic coefficient 100 in canonical e units is not the
strongest consequence of the old angular proof. Retaining its actual mesh
Delta in the sufficient inequality gives

$$
2(1-\tau)\eta\ge\frac74\tau+
\frac{\Delta}{4\tau}+\frac\Delta4.                 \tag{P6}
$$

The printed coarser condition (obtained using Delta<=tau^2) gives leading
eta=tau and canonical cubic coefficient 16. Keeping the actual mesh
Delta asymptotic to tau^2/4 on the source count schedule improves this to
eta asymptotic to 29tau/32 and coefficient 29/2. With Delta=o(tau^2), the
coefficient is 14. All three are prior-art corollaries and must be included
when discussing the frontier.

The angular exact-area lower bound proved in the radial/angular comparison
note is

$$
R\ge\frac12-\frac{\tau^2}{240}
 +\eta\tau^2(2-3\tau^2/4)-\frac{\tau^4}{40}.
\tag{P7}
$$

Condition (P6) forces 0<tau<1 and eta>=7tau/8. Substitution gives a
cubic coefficient at least
(7/8)(2-3tau^2/4)-tau/40 >=171/160>1. Hence even this broader, optimized
published sufficient range obeys

$$
R\ge\frac12-\frac{\tau^2}{240}+\tau^3
\ge\frac12-\frac1{93\,312\,000}.                    \tag{P8}
$$

The final minimization is over all tau>=0, at tau=1/360. The stated cubic
family outside this sufficient small-tilt route has the separate large-tilt
bound in the comparison note. Thus the comparison does not select the
unnecessarily large coefficient of Proposition 6.1 as its only baseline.

## 4. Scope of the completed benchmark

SECANT-THEOREM.md supplies a closed-body cover with 20000 triangular cylinders
and R<0.499929. Its actual maximum axis tangent is
sqrt(3)*(1/10)*(1-1/10000). Bounds (P3), (P5), and (P8) are strictly above
that cost. The direct angular certificates exceed the count budget.

The prescribed rational/singular full retained-grid, rational product/log,
nilpotent apex-list, and shortened-beam constructions have the separate
actual-area, count, or angle obstructions proved in
`../verification/published-generic-comparison.md`. They allow the benchmark's
finite-axis budget and use the published coordinate and error conventions.
Together these compare the audited source recipes at at most 20000 cylinders
and at most the new physical tilt; the radial and generic lower bounds even
allow the slightly larger tangent budget sqrt(3)/10.

The result does not claim domination over every admissible instance of a
generic approximation theorem. In particular, new admissibility proofs can
extend the source's algebraic families beyond their old proved ranges. The
eta=1/1000,tau=1/5 example is now such an extension, proved by the new
quartic/secant certificate. It is not a cover certified by the older bounds.
Likewise deleting retained grid tiles, changing the product shapes or their
error allocation, or optimizing arbitrary new source instances is outside
the chosen published count conventions. These restrictions were explicitly
selected by the user; they are not a global lower bound for all cylinder covers.
