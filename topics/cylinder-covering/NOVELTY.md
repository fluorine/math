# Novelty specification — 15 October 2026

The initial specification below was written before numerical experiments.
Final update: the quartic certificate, sharp enclosure result and stronger
finite secant theorem are complete, with independent rational certificates.
The identified explicit published sufficient ranges and count conventions
are compared in RESULT.md and research/published-proof-ranges.md. The record
below preserves the successive candidate specifications and audit corrections;
claims marked as an initial question are historical, not current gaps.

## Pinned evidence

All four requested manuscripts are pinned to OpenAI math revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, also the public default-branch
head checked on 15 October 2026. See `sources/manifest.json` for original URLs,
Git blob IDs and SHA-256 hashes. Sources retain their upstream license.

The source audit includes the angular paper's compatible caps, nonuniform
partitions and Proposition 6.1; radial Theorem 1.1 and Appendices B–D,
especially the exact finite footprints; the ruled-set approximation theorem;
and the slope-field rational, singular and square-zero constructions.
Public searches found no matching completed improved effective finite package.
This is limited search evidence, not a guarantee of novelty.

## Physical normalization and resource convention

The body is exactly
`K={(x,y,sqrt(2)*s): 0<=s<=1, |x|<=1-s, |y|<=s}`.
Its edges have length 2 and its minimum orthogonal projection area is sqrt(2).
Cost R is the sum of all perpendicular base areas, counted with multiplicity,
divided by sqrt(2). Cylinders are infinite along their axes.

For calculations use canonical coordinates `(X,Y,sqrt(2)*t)` with
`|X|<=1+t`, `|Y|<=1-t`, transported to K by
`(x,y,z)=(X/2,-Y/2,(sqrt(2)-sqrt(2)*t)/2)`.
This is a similarity of ratio 1/2, with two coordinate sign changes. Its area scale
is 1/4, so normalized cost is unchanged. Canonical tilt is e; the physical
slope convention in the angular paper is tau=2e. The limiting first-family
axis on K is `(1,tau*(1+q^2)/4,sqrt(2)*tau*q/2)` after relabeling the canonical
angular variable by its negative. Equivalent orthogonal images have the same
cost. The actual finite axis vectors will be specified, not inferred from
parameter names. Maximum angular deviation can also be recovered from them.

The primary bases are compact nondegenerate perpendicular triangles. Count is
the number of cylinders including both families: exactly 2N for N intervals.
The generator stores a constant number of rational coefficients; their bit
lengths grow as O(log N) for fixed rational tilt. Cylinders are obtained by index.
Other source base classes are disclosed and included in the comparison audit;
there is no claim that missing count bounds imply inferior constructions.

## Original proposed target, recorded before experiments

Let G(q)=(1+q^2)/2, H(q)=q^2*G(q), D0(q)=G(q)^2+2q^2.
For every `0<e<=1/100`, investigate the cap
`C_e(q)=1+e^2*H(q)+(9/16)*e^4`.
For every integer `N>=1`, seek explicit midpoint triangular footprints for
the two capped sweeps that cover the entire closed body, with an exact finite
area sum and a uniform bound in e,N. On the schedule
`N=ceil(2/e^2)=ceil(8/tau^2)`, the target is

`R_N <= 1/2 - e^2/60 + (5/2)*e^3 + C*e^4`

for an explicit modest absolute C and explicit saving interval. A general
mesh/error bound must imply this schedule, not merely a fitted asymptotic.
Constants and intervals above remain conjectural until independently checked.

The proposed mechanisms were (1) elimination of the spatial
coordinates before the cap-failure estimate, followed by completion of a
square, which can reduce cubic padding to quartic; and (2) retention of the
correlation between radial and transverse errors in a frozen triangle.
The leading coefficient 1/240 is existing prior art and is not claimed new.
Neither a change of scale nor a parameter substitution alone is a contribution.

## Baselines and acceptance boundaries

Angular Proposition 6.1 uses the same count schedule and gives
`|R-1/2+tau^2/240-(25/2)*tau^3|<=2*tau^4` on its stated interval.
It is not the sole baseline. Its variable-margin corollaries and compatible
cap theorem must also be considered.

Radial Appendix B already gives cubic caps
`1+e^2*H+c*e^3` for every e>0 and c>=9/2. The best stated cubic member has
limiting cost `1/2-e^2/60+(9/2)*e^3+O(e^4)`, or cubic coefficient 9/16
in physical tau units. Appendix C already gives exact finite triangle,
trapezoid and nonconvex polygon areas, including sharper sufficient footprint
constants than some illustrative table rows. Actual swept projections are also
source bases and can be smaller than displayed enclosures.

Fixed-margin linear and square-root caps have freely chosen beta>0;
fractional caps also occur. A comparison must state their admissibility
condition at the same tilt, and must not select only unfavorable examples.
At the time of this initial specification, the inspected general ruled-set
and slope-field constructions had no completed comparison in the present
physical tilt and cylinder budget; the final comparison is recorded below. Their associated
Lean library does contain generic explicit rate and count machinery, as detailed
below; neither unspecified application constants nor missing comparisons prove
that those constructions lose at a given finite budget.
Shortened beams have a different normalization and require an explicit physical
tilt dictionary and inclusion of their strip cylinders.

Merely making the source's existing footprint bounds effective is retired as
an insufficient standalone novelty target. Proving the new cap/enclosure and
beating all source constructions certified by the common radial padding
criterion would be a substantive bounded theorem. It would NOT by itself
settle the user's broader requirement to beat every relevant source
construction. That comparison was retained as an explicit obligation during research; any
unfinished part was to remain marked incomplete. Its final quantified scope
is now documented in RESULT.md and research/published-proof-ranges.md.

## Search scope and classification

The independent audit checked current GitHub history and public follow-up
searches by exact titles and radial/finite-mesh/count terminology. The current
radial path history has only its initial manuscript commit. Unindexed,
unpublished or inaccessible work is not ruled out. Final results will separate
source corollaries, newly proved estimates, conditional comparisons and
numerical evidence. A fresh novelty check is required for a change of target.

## Result and corrected novelty classification

THEOREM.md proves coverage for the quartic cap on 0<e<=1 and proves 9/16 is
sharp among constant quartic corrections. Its finite triangular realization
has explicit error/count bounds on 0<e<=1/10. At e=1/10,N=10000, its 20000
cylinders have rigorously enclosed normalized area
[0.499947504745824,0.499947504745984]. The same-count small-tilt comparison
beats the strongest stated cubic radial cap, including its actual projected
bases, when using the same uniform midpoint partition and axes.

The first proposed smaller triangle, with effective padding (5/2)e*d, is
an immediate completion of a source trapezoid. It is a source corollary,
not a new mechanism. The retained triangle uses the cap-dependent slope
ell=(d/2)(1-e*d/M), whose exact area is bounded by d(M+2e*d)^2/2.
The principal advance is the exact overlap elimination and quartic certificate;
the useful finite package combines it with this refined enclosure.

At one fixed tilt the new cap is syntactically a source linear cap with
beta=(9/16)e^2. The source's fixed-beta theorem does not allow this substitution
uniformly, and its explicit common padding criterion fails throughout the
new interval. The new assertion is a stronger proven feasibility range and
sharp quartic estimate, not a renamed algebraic cap family.

### Associated Lean prior art, audited after the manuscripts

The pinned files under `sources/lean/OAI/Geometry/CylinderCovering/` include:

- `Physical/FootprintRate.lean`: explicit equal-mesh O(1/N) bounds with full
  constants for absolute and affine feet, relative to the sampled cap sum.
- `Nilpotent/RateUniform.lean` and `RateCertificates.lean`: a uniform-in-tags
  smooth square-zero field error bound by boundary-grid excess plus C*delta.
- `Nilpotent/RateCost.lean`, `RetainedArea.lean`, `RateAssembly.lean`, and
  `RatePhysical.lean`: retained-index counts, area bounds, and exact physical
  realization. Combining these source estimates directly gives a generic
  count bound `(2B+4)^2*[1+2(L+sqrt(2))*delta]^2/delta^4`, where
  `L=(1+M)*(sqrt(2)+K)` and D lies in [-B,B]^2. The constants depend on
  the fixed field and derivative bounds.

Consequently generic finite approximation, explicit footprint rates, and
generic nilpotent count control are all prior art. Merely claiming that no
source quantitative rates exist would be false. The manuscript-only audit
was never a complete audit of all formalization artifacts.

The inspected `Radial/OverlapBounds.lean` retains the cubic 9e^3 error;
`Radial/CapsDefinitions.lean` lists the existing four cap types.
`Footprints/QuadraticPhysicalFootprints.lean` and `Physical/Triangles.lean`
do not contain the new cap-dependent triangle slope in their inspected
formulas. No matching quartic certificate or its sharpness result was found
in the targeted dependency audit. This is not an exhaustive search of every
Lean module; no Lean compilation or axiom audit was performed.

## Follow-up question: exact finite enclosure optimality

At this stage of the audit, the manuscript-only reading had not recovered a
numerical witness for the arbitrary fixed-margin angular family. Its area
could be smaller than the first 20000-cylinder example at unverified parameters.
The later source-proof audit recovered explicit witnesses, and the new secant
proof below certified the previously conditional candidate. This earlier gap
motivated the next two investigations; it is not the final status.

A separate analytical question is being audited before any experiment: for
fixed a,k,M>0 with z=ka/M<=1/5, minimize the area of a triangle
`u<=U, |W|<=ell*(u+V)` over all ell>0,U,V that contain the whole frozen set

    u=rho-s*b, W=b*rho-s*b*b/2,
    |b|<=a, |s|<=k, 0<=rho<=M.

The candidate minimizer is the already constructed reduced-slope triangle
ell=a-ka*a/M, U=M+ka, V=ka+ka*a/(2ell). This is an exact finite enclosure
class, with a specified symmetry axis and one perpendicular side; it is not
the source's previously determined compatible-cap class, and it makes no
claim about all triangles, actual projected bases, or all cylinder covers.
Physical area is multiplied by the fixed nonsingular projection factor, so
the coordinate-area minimizer is also the physical-area minimizer for that
frozen axis. A further finite-budget statement would have to optimize the
sum over a precisely specified partition class, rather than relabel this
single-cell problem as full finite-budget optimality.

The completed fresh audit found no variable-opening minimum-area or uniqueness
theorem in the footprint appendix, freezing section, or inspected
`Footprints.lean`, `Shapes.lean`, and `CertificatesDefinitions.lean` modules.
Those modules are now pinned too. The main compatible-cap theorem does not
optimize enclosing triangles. Targeted public searches found no matching
result; this is not an exhaustive minimum-enclosing-triangle literature audit.

The exact minimization proof is now in THEOREM.md, Theorem 3. Three actual
sweep points force piecewise lower bounds whose unique minimum is the stated
triangle. Theorem 4 goes beyond summing fixed-cell minima: over every midpoint
partition with N cells and all symmetric enclosing triangles for the full
cell-maximum sweeps, it proves a uniform finite lower bound with leading loss
4e/N. The uniform partition attains that leading coefficient. At
N=ceil(2/e^2), the cubic coefficient 2 is sharp in this explicitly enlarged
enclosure class. This does not assert optimality for the true variable-cap
sweeps or unrestricted covers. The original goal and the then-outstanding source comparison remained recorded;
this separate result did not silently replace them.

## Pre-experiment specification: compatible secants with a quartic buffer

The sharp finite enclosure result identifies a reason to change discretization
within the original research objective. The next analytical candidate retains
the source's compatible secant boundaries, substitutes the new quartic cap,
and pays explicitly for the difference between its discrete and continuous
overlap weights. No experiment had been run for this candidate when this specification was recorded.

For a cell centered at c with half-width a, use secant coefficients
A=G(c)-a^2/2 and b=c. Exact elimination of the two selected intercept equations
again gives a weighted cap inequality. Its difference from the continuous
quartic certificate is expected to be O(e*d), where d is the maximum cell
width. A uniform additive cap buffer can absorb that error. Maximum caps on
each cell would give exactly 2N compact triangular bases with compatible sides,
without requiring each triangle to enclose a full continuously tilted sweep.
Thus this mechanism lies outside the enclosure class of Theorem 4.

The possible novelty is a quantitatively certified admissible cap/count range,
not the algebraic form of the secant axes or the triangular bases. The source
already has both, as well as fixed-positive-margin asymptotics. Any new claim
must prove the vanishing-margin overlap, explicit discrete remainder and the
same physical normalization, rather than substitute a tilt-dependent margin
into a fixed-margin theorem. The numerical candidate eta=1/1000,tau=1/5,N=10000
is a useful first feasibility test because its area is rigorously lower but
its coverage has not yet been established.


## Final result of the secant investigation and source-range audit

SECANT-THEOREM.md proves the candidate. For every positive partition and
0<e<1, a cell of half-width a has sufficient canonical cap padding

    delta = [M_*(e+e^2/2)*a + 2e^2*a + (M_*e^2/2)*a^2]/(1-e).

It follows from exact discrete elimination and a uniform perturbation bound
against the quartic square certificate. For e<=1/10 the area error is at most
e times the mesh. Equal cells give |R-J|<=2e/N and the explicit saving count
N>=ceil(480/e). On N=ceil(2/e^2),
R<=1/2-e^2/60+e^3/2+(9/2)e^4, with saving throughout e<=1/50.
Independent exact evaluation at e=1/10,N=10000 gives
[0.499921585997001674,0.499921585997001774]. This is the preferred finite
realization. It also proves feasibility of the earlier conditional angular
candidate at eta=1/1000,tau=1/5.

The old angular proof itself has stronger corollaries than Proposition 6.1:
optimizing its printed budget gives canonical cubic coefficient 16; retaining
the true mesh on that proposition's schedule gives 29/2; letting the mesh be
o(tau^2) gives 14. These are included as prior art. The new coefficient 1/2
therefore is not a comparison only to the proposition's coefficient 100.
The source radial common criterion's smaller coefficient 9/2 and its actual
projected bases are included in the finite comparison as well.

The source Lean proofs give the general compatible-cap witness
(10+4E)tau<=eta<=1/480 and actual-area remainder (6E+2)tau^4. These imply an
actual-area floor above 0.499999999819 and a full-list count at least
36864000. Separate quantitative maximum/cubic, endpoint, squared-direct and
Cartesian certificates are audited individually. The radial explicit ranges
all imply or contain a cap satisfying the 9e overlap criterion. The generic
retained-grid, product/log, nilpotent and beam recipes have the actual-area,
count or angle obstructions detailed in the comparison notes.

The user selected published proved parameter ranges and count conventions.
The completed numerical comparison uses the identified explicit sufficient
ranges furnished by the source proofs. It does not assert that every possible
witness of an existential theorem satisfies those numerical thresholds, or
that a wider range cannot be valid. Nor does it compare every newly admissible
instance of a generic method, arbitrary changes to its tile selection or error
allocation, or all cylinder covers. The fresh targeted audit found no matching
quartic/secant certificate or sharper quantified admissible range in the
inspected source dependencies; that remains search evidence rather than a
guarantee of novelty. No Lean compilation or exhaustive proof search is claimed.
