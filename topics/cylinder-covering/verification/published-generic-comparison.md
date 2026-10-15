# Published finite realizations: independent count and angle comparison

The published beam, square-zero, rational, and singular constructions considered
below do not match the new cover's **20,000 cylinders, physical angle budget,
and normalized cost below (1/2)** on the prescribed realization and error
conventions. These conclusions use actual axes, explicit list counts, and
geometric area lower bounds. An unspecified convergence constant is never
treated as a lower bound.

The benchmark below is the earlier radial-triangle cover. The subsequently
verified [secant cover](secant-report.md) has the same 20,000 count, satisfies
the same angle allowance, and has still smaller cost. Every obstruction in
this note therefore applies to that stronger benchmark as well.

## Comparison being made

Normalize total perpendicular base area by the tetrahedron's minimum
projection area (A_{min}). Similarities preserve this ratio, angles, and
counts. The new cover at (e=1/10,N=10000) has 20,000 cylinders and independently
certified ratio

$$
0.499947504745824\le R_{\rm new}\le0.499947504745984.
$$

Its largest finite tangent of deviation from the corresponding opposite-edge
direction is

$$
e\sqrt{G(1-1/N)^2+2(1-1/N)^2}<\sqrt3/10,
\qquad G(q)=(1+q^2)/2.
$$

We give the source constructions the slightly larger allowance
$\Theta=\arctan(\sqrt3/10)$. Every retained axis assigned to one of the
two equality-edge directions must satisfy this allowance. Thus its physical
projection cosine exceeds (49/50), since
$(49/50)^2(103/100)<1$. This is a condition on the **actual finite list**,
not a condition on the entire underlying vector field.

Counts include both families, auxiliary cylinders, and repeated entries from
different coarse squares, just as in the published constructions. For the open
product/logarithmic construction, the count is that of the selected finite
subcovers; the initially countable cover is not counted as a finite list.

| Published realization | Obstruction at the stated benchmark |
|---|---|
| Shortened beams plus central strip | A necessary strip axis exceeds the angle allowance. |
| Square-zero slope field plus published apex net | Apex lists alone have at least 34,134 entries. |
| Rational or singular fields with the full retained square-grid lists | If the list has at most 20,000 entries and satisfies the angle budget, its actual ratio is at least (637/1250=0.5096). |
| Rational product/logarithmic cells with the published saving-error allocation | Any selected finite cover satisfying the angle budget needs more than 20 million main cell cylinders in one family. |

The last row uses the published sufficient allocation of approximation error
for a saving below (1/2). It does not rule out an accidental saving from a
different error allocation whose advertised guarantee is worse.

## 1. Beam-strip axes

The pinned [beam manuscript](../sources/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/build/beams.tex)
uses physical coordinates (P(x,y,t)=(x/\sqrt2,y/\sqrt2,t)), with vertices
$P(\pm2,0,-1),P(0,\pm2,1)$, and (0<a<1/2). Its six unoriented edge
directions are the two horizontal coordinate axes and the four directions with
unit representatives $(\pm1/2,\pm1/2,1/\sqrt2)$.

For a strip tag (t\in[-1,1]), put

$$
b=at-a^2t^3,\qquad w=(1+b,1-b).
$$

The strip cylinder axis is horizontal and perpendicular to (w), so it is
parallel to $(-(1-b),1+b,0)$. Since $|b|<1/2$, its angle to the closer
horizontal edge has tangent

$$
\frac{1-|b|}{1+|b|}>\frac13>\frac{\sqrt3}{10}.
$$

Its angle to any slanted edge is at least (\pi/4): the horizontal component
of the corresponding unit edge vector has length (1/\sqrt2). Thus even
reassigning an edge or applying a tetrahedral symmetry does not fix the angle
violation. The strip is nonempty, since its specified width at (t=0) is
(a+25a^3>0). The published beam-strip construction therefore supplies no
admissible competitor at this angle budget, regardless of its count or area.
The same conclusion holds for every (0<e\le1/10).

## 2. Square-zero completion: the apex lists already exceed the budget

The pinned [square-zero construction](../sources/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/nilpotent.tex)
sets

$$
c=\tfrac12,\quad v(p)=\frac{1+p^2}{4},\quad w(p)=\frac p2,
\quad a(p)=c^2p^2v(p),\quad H(p)=\tfrac12+k^2a(p)+k^3,
$$

and

$$
I(k)=\int_{-1}^1\frac{H(p)^2/2}{\sqrt{1+k^2(v(p)^2+2w(p)^2)}}\,dp.
$$

Its proved finite saving completion chooses

$$
0<\epsilon<\Delta(k):=\tfrac14-I(k),\qquad
0<\rho<\frac{\epsilon}{32(1+k/2)^2}.
\tag{1}
$$

For **each** sign, the printed apex-net recipe uses all tags
$p_j=-1+2j/m$, (0\le j\le m), where (m=\lceil2/\rho\rceil).
These are (m+1) distinct cylinders per family when (k>0). The endpoint
axis tangent is $\sqrt3 k/2$; an angle allowance
$\arctan(\sqrt3 e)$ therefore requires (k\le2e).

Since (H\ge1/2) and (v^2+2w^2\le3/4), the elementary inequality
$(1+x)^{-1/2}\ge1-x/2$ gives

$$
I(k)\ge\frac1{4\sqrt{1+3k^2/4}}\ge\frac14-\frac{3k^2}{32},
\qquad \Delta(k)\le\frac{3k^2}{32}.
$$

If $\Delta\le0$, the published choice (1) is unavailable. Otherwise its
two apex lists alone have

$$
2(m+1)>\frac4\rho>
\frac{128(1+k/2)^2}{\Delta(k)}
\ge\frac{4096}{3k^2}\ge\frac{1024}{3e^2}
\tag{2}
$$

entries. At (e=1/10), this exceeds (102400/3), hence is at least 34,134.
The retained grids only add to that count. More generally (2) exceeds the
new schedule (2\lceil2/e^2\rceil\le5/e^2) for (0<e\le1/10).

This is a count obstruction for the **published full net and tolerance
choice**. It is not a lower bound for an optimized replacement apex cover,
or for pruning the printed lists by a new argument. The source's statement
that a net of at most (m+1) cylinders exists does not by itself prove a
minimum-cardinality theorem; the conclusion here concerns its explicit net.

## 3. Mandatory retained collar in the published square-grid recipe

The [ruled-set proof](../sources/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/build/sections/finite-approximation.tex)
chooses all coarse squares of side (\delta) meeting (D), uses fine spacing
$\tau=\delta^2$, and retains **all** fine-grid centers within distance

$$
R_\delta=C(\tau+L\eta_\delta\delta),\qquad
C=\frac{1+LM}{\sigma}\ge1,\qquad0<\sigma\le1
$$

of the whole coarse square. Thus (R_\delta\ge\tau). The fine tiles are
squares of side (\tau) in an orthonormal frame, as specified by
[the affine covering lemma](../sources/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/build/sections/linear-coverings.tex).

Fix one coarse square (S). Any point within (\tau/4) of (S) belongs
to a fine tile whose center is at distance at most
$\tau/4+\tau/\sqrt2<\tau\le R_\delta$ from (S). Its center is
therefore retained. The retained tiles cover (S) and its four exterior
side strips of width (\tau/4), a set of area at least
$\delta^2+\delta\tau$. Their interiors are disjoint within this lattice.
Adding over coarse squares, **with the source's multiplicities**, yields

$$
n\delta^4\ge |D_{\rm grid}|(1+\delta).
\tag{3}
$$

This lower bound is independent of the modulus of continuity and all
unquantified smallness thresholds.

### Physical scaling and domain area

The source permits applying the recipe in native labels, with physical map
(T_h=\operatorname{diag}(1,h)), or after moving to orthonormal physical
labels. In the latter convention the grid domain area is (h|D|), rather
than (|D|). In every case below a safe common bound is

$$
|D_{\rm grid}|>1/16.
\tag{4}
$$

For the [rational field](../sources/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/rational.tex),
(h=1/\sqrt2), (A_{\min}=h/2), and (D\supset D_0) with
(|D_0|=1/8). Even after (T_h), (h/8>1/16).

For the [singular field](../sources/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/singular.tex)
in its edge-two normalization, (h=\sqrt2), (A_{\min}=h), and the two
tip cylinders have normalized total area (8d^2). If (d\ge1/4) these
already cost at least (1/2). For (d<1/4), each grid domain contains
$\{d\le r\le1/2, |b|\le r\}$, of area
$1/4-d^2>3/16$. In its published edge-one normalization the corresponding
facts are (h=1/\sqrt2), (A_{\min}=h/2), tips costing (8\sigma^2),
and a contained set of area (1/8-\sigma^2/2>3/32) when (\sigma<1/4).
After physical scaling this last lower bound is
$3/(32\sqrt2)>1/16$. Thus (4) accounts for both coordinate conventions.

If the total count is at most 20,000, (3) implies, for each nonempty family,

$$
\delta^4>\frac1{16\cdot20000}>\frac1{25^4},\qquad\delta>\frac1{25}.
$$

All **actual finite** axis projection factors exceed (49/50) under the
comparison angle budget. Consequently the normalized cost of each grid is
at least its normalized domain area multiplied by

$$
g=\left(1+\frac1{25}\right)\frac{49}{50}=\frac{637}{625}>1.
$$

For the rational construction the two grids therefore cost at least
$4g(1/8)=g/2$. For the singular edge-two version, grids and tips cost
at least

$$
2g(1/4-d^2)+8d^2=g/2+(8-2g)d^2\ge g/2.
$$

The edge-one version gives the identical expression with (d) replaced by
$\sigma$, from $4g(1/8-\sigma^2/2)+8\sigma^2$. All three actual
ratios are therefore at least

$$
\boxed{637/1250=0.5096}.
\tag{5}
$$

The same argument excludes the small-(e) schedule uniformly. If
$B\le2\lceil2/e^2\rceil\le5/e^2$ and (0<e\le1/10), then
(3)--(4) give $\delta^4>e^2/80>e^4$, hence $\delta>e$. Replace
(g) by $(1+e)/\sqrt{1+3e^2}>1$, and the displayed cost bounds are
strictly above (1/2).

The pinned Lean files `Nilpotent/RateCertificatesDefinitions.lean`,
`Nilpotent/RatePhysical.lean`, and `Nilpotent/RetainedArea.lean` preserve
the retained-index multiplicities and exact cardinality cost; the smooth-rate
collar is also at least (\delta^2). They supply effective upper estimates,
not an optimization over smaller lists. The obstruction here is the direct
geometric lower bound (3). Deleting or merging retained tiles, trimming coarse
squares, changing the fine/coarse mesh relation, or rescaling the canonical
input before selecting its mesh would be a different realization; none is
silently included in (5).

## 4. Product and logarithmic cells after finite subcover selection

The rational paper explicitly publishes [two additional finite realizations](../sources/Slope-field-perturbations-of-the-two-cylinder-covering-September-27-2026/build/sections/dictionary.tex),
using the [product/logarithmic theorems](../sources/Finite-cylinder-approximation-of-ruled-sets-September-27-2026/build/sections/product-methods.tex).
The following argument covers both, including their final finite subcovers.
It does not require a tilt bound on discarded cells or on the whole field.

### A lower integral bound from the necessary spectral hypothesis

In centered edge-one labels, (r=1/2-T), (|Y|\le r/2), and

$$
a=-\frac{Y^2}{4(r+d)^2}-\frac{r(r+2d)}{16(r+d)^2},\qquad
b=\frac{Y}{2(r+d)},\qquad h=1/\sqrt2.
$$

The eigenvalues of (D(\epsilon W_d)) are
$\pm\epsilon d/[4(r+d)^2]$. The theorem's strict spectral hypothesis
with axial half-length (1/2), evaluated at the included apex (r=0),
necessarily gives (\epsilon<8d). On (D_0), where (r\le1/2),

$$
|a|\le\frac r{8(r+d)},\quad |b|\le\frac r{4(r+d)},\quad
\epsilon\sqrt{a^2+h^2b^2}<\frac{\sqrt3 rd}{r+d}\le\frac{\sqrt3}{2}.
$$

Thus (j=(1+\epsilon^2(a^2+h^2b^2))^{-1/2}>2/\sqrt7>3/4) on
(D_0). The normalized limiting integral of **each** family satisfies

$$
A=\frac{h\int_Dj}{A_{\min}}=2\int_Dj>\frac3{16}.
\tag{6}
$$

The logarithmic construction is exactly similar to these coordinates: its
dictionary is (d=d_0/2), $\epsilon=4(1+d_0)k$, with every area
multiplied by (1/8). Its spectral condition at (s=0) gives
$k(1+d_0)/d_0<1$, again exactly $\epsilon<8d$. Hence (6) applies
to both published parameterizations, including fixed quadratic padding.

### The prescribed error tolerance forces exponentially thin cells

To certify a saving, the source chooses normalized finite errors
$E_1+E_2<1/2-2A<1/8$. At least one family has (E_i<1/16). Its
product/logarithmic proof requires

$$
[(1+\eta)^2-1]A<E_i/2<1/32.
$$

By (6), $(1+\eta)^2-1<1/6$, so (0<\eta<1/12). For its cell shape
$Q_\tau$ and open intercept patch $P_{\tau,\gamma}$, the proof
also requires $\gamma>0$, $(1+\gamma)\tau<1$, and

$$
R(\tau,\gamma)=\frac{|P_{\tau,\gamma}|}{|Q_\tau|}\le1+\eta.
$$

The numerator increases with $(1+\gamma)\tau$ in this range. Writing
$L=\log(1/\tau)$, we obtain

$$
R(\tau,\gamma)\ge R(\tau,0)=1+\frac{\log9}{1+L},
\qquad L>12\log9-1>25.
\tag{7}
$$

For the last strict inequality one can use
$\log3=2\operatorname{arctanh}(1/2)>1+1/12=13/12$.

### No finite subcover of the permitted size can cover its intercept plane

Each selected parameter cell is $G=p+\rho L_pQ_\tau\subset D$, with
unit eigenvectors as the columns of (L_p). It contains
$p\pm\rho v_i$, so $\rho\le\operatorname{diam}(D)/2$, and
$|\det L_p|\le1$. As $|Q_\tau|=4\tau(1+L)$, its associated
open intercept patch has normalized physical area at most

$$
\frac{h\operatorname{diam}(D)^2}{A_{\min}}
(1+\eta)\tau(1+L).
\tag{8}
$$

The prefactor in (8) is less than three in all published coordinate forms.
In native centered labels, (D\subset[-3/8,3/8]\times[-1/4,1/2]), so
it is at most (2(9/8)=9/4). After (T_h), it is at most
$(2\sqrt2)(27/32)<3$. In the logarithmic paper's orthonormal labels,
$U_k\subset[-3/(2\sqrt2),3/(2\sqrt2)]\times[0,3/2]$, and
$A_{\min}=2\sqrt2$, giving $27/(8\sqrt2)<3$. These are the same
geometry up to the stated similarity.

Since $(1+L)e^{-L}$ decreases for (L>0), (7)--(8) imply that each
selected main patch has normalized intercept area less than

$$
3\cdot\frac{13}{12}\cdot26e^{-25}
<\frac{169}{2}\left(\frac38\right)^{25}<10^{-8},
\tag{9}
$$

where $\exp(1)>8/3$ follows from its power series. This is a bound on
intercept area, before any projection weight, and uses no field-wide tilt
assumption.

The prescribed residual disks have normalized perpendicular cost
$<E_i/2<1/32$. The selected residual axes satisfy the comparison angle
budget, so their total normalized intercept area is less than
$25/784$. Discarding disks in a finite subcover can only decrease it.
At axial coordinate zero, the cylinders of this family must cover (D_0),
whose normalized physical intercept area is (1/4). With at most 20,000
selected main cells their union has area less than

$$
20000\cdot10^{-8}+\frac{25}{784}<\frac14,
$$

a contradiction. In fact (9) forces more than

$$
\left(\frac14-\frac{25}{784}\right)10^8
=\frac{171}{784}\,10^8>20{,}000{,}000
$$

selected main cell cylinders in this family alone. This count obstruction
survives both the product proof's countable packing and the logarithmic
proof's finite stopping rule.

## Scope and remaining gaps

No inspected published construction defeats the fixed benchmark on the stated
angle, count, parameter-range, and realization conventions. The arguments do
not establish an optimal cylinder cover or dominance over every possible
application of the generic ruled-set theorem.

- The grid and apex results concern the prescribed full lists. Their constants
  are not lower bounds for redesigned meshes, omitted tiles, or optimized
  endpoint coverings.
- The product/logarithmic result concerns the published saving-error allocation
  and separate finite covers of the two sweeps. It allows arbitrary finite
  subcovers within those two applications, but not a newly optimized joint
  pruning argument that ceases to cover each swept set separately.
- The singular paper explicitly invokes the compact square-tile construction.
  A new product/logarithmic application to a singular field is a further
  generic instance, not one of the published finite realizations compared here.
- For the schedule (2\lceil2/e^2\rceil), the beam, apex, and grid exclusions
  hold uniformly for (0<e\le1/10). The product/logarithmic bound is a fixed
  count obstruction; it applies whenever that schedule is at most 20 million,
  but does not settle its arbitrarily small-(e), unbounded-count tail.
- Mere absence of an explicit upper count theorem would not prove any of these
  comparisons. The numerical constants above come from explicit geometric
  bounds and the printed recipe's inequalities.

All displayed rational threshold comparisons were checked with exact
`fractions.Fraction` arithmetic. The source interpretation and geometric
arguments are mathematical proofs; they are not claimed as Lean kernel checks.
