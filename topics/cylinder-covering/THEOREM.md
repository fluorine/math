# Quartic radial overlap and effective finite triangular covers

The stronger compatible-secant realization is now in [SECANT-THEOREM.md](SECANT-THEOREM.md). This manuscript retains the original radial realization and its sharp full-sweep enclosure results.
Research manuscript, 15 October 2026. The statements below concern a specific
explicit construction. They do not assert optimality among arbitrary cylinder
covers, or dominance over every construction in the four source papers.
The source comparison proved here is stated precisely in Section 7.

## 1. Body, physical axes, and statement

Let H=sqrt(2) and
$$
 K=\{(x,y,Hs):0\le s\le1,\ |x|\le1-s,\ |y|\le s\}.
$$
Its four vertices are (±1,0,0),(0,±1,H); all six edges have length 2.
A cylinder is B+R v, with nonzero v and compact base B in v-perp. Its
cost is the Euclidean area of B. All costs are summed with multiplicity.
Write R for total cost divided by A_min(K)=H.

Define, for -1<=q<=1,
$$
 G(q)=(1+q^2)/2,\quad h(q)=q^2G(q),\quad
 D_0(q)=G(q)^2+2q^2,\quad
 C_e(q)=1+e^2h(q)+\frac9{16}e^4.
$$
The lower physical axis at q is (1,eG(q),Heq); the upper one is
(-eG(q),1,Heq). Thus the source angular slope parameter is exactly tau=2e.
The tangent of deviation from the corresponding edge direction is
e*sqrt(D_0(q)); on the whole field its maximum is sqrt(3)*e.
This is a physical direction statement, not a rescaling of the body or cost.

**Theorem 1 (explicit finite cover).** For every 0<e<=1/10 and every positive
integer N, the triangles in Section 3 give exactly 2N labeled cylinders
covering every point of the closed K. They have compact nondegenerate
perpendicular triangular bases. Let R_N(e) be their normalized total area,
and put
$$
 J(e)=\frac14\int_{-1}^1\frac{C_e(q)^2}{\sqrt{1+e^2D_0(q)}}\,dq.
$$
Then
$$
 |R_N(e)-J(e)|\le\frac{6e}{N},                                      \tag{1}
$$
and the sharper uniform upper bound is
$$
\begin{split}
 R_N(e)\le {}&\frac12-\frac{e^2}{60}+\frac{929}{1260}e^4+4e^6\\
 &+\frac{4e}{N}+\frac{8e^2}{N}+\frac{81e^3}{20N}
       +\frac{8e^2}{N^2}.                                           \tag{2}
\end{split}
$$
In particular:

- For N>=ceil(1440/e), R_N(e)<=1/2-e^2/240.
- At e=1/10,N=10000 there are 20000 triangular cylinders and
  R_N(e)<1/2-1/25000=0.49996.
- For 0<e<=1/10 and N=ceil(2/e^2)=ceil(8/tau^2),
  $$
  R_N(e)\le\frac12-\frac{e^2}{60}+2e^3+\frac52e^4
  =\frac12-\frac{\tau^2}{240}+\frac{\tau^3}{4}
       +\frac5{32}\tau^4.                                          \tag{3}
  $$
  This last schedule gives R_N<=1/2-(19/37500)e^2<1/2 for 0<e<=1/125.

For a nonuniform midpoint partition with maximum width delta, the same
construction and proof give |R-J(e)|<=3e*delta. Its count is twice its
number of positive-width intervals.

The compact generator `construction.py` returns any cylinder by index using
rational arithmetic for rational e. Coordinates are stored as (x,y,z/H),
whose metric is diag(1,1,2); no irrational coordinate approximation is needed.
It stores a constant number of rational coefficients with respect to N;
their bit lengths grow as O(log N) for fixed rational e.

## 2. Complete overlap proof with a quartic buffer

Use canonical physical coordinates (X,Y,Ht) for
K4={|X|<=1+t, |Y|<=1-t}. The similarity
$$
 (X,Y,Z)\longmapsto(X/2,-Y/2,(H-Z)/2)                                \tag{4}
$$
takes K4 onto K and divides all areas by four. The upper and lower sweeps
in K4 are
$$
 (X,\rho q-eXG(q),H(1-\rho+eXq)),\quad |X|\le2,\ |q|\le1,
       \quad0\le\rho\le C_e(q),                                    \tag{5}
$$
$$
 (\sigma p+eYG(p),Y,H(-1+\sigma+eYp)),\quad |Y|\le2,\ |p|\le1,
       \quad0\le\sigma\le C_e(p).                                  \tag{6}
$$
The orthogonal map (X,Y,Z)->(Y,-X,-Z) takes one to the other and preserves K4.
Their parameter domains are compact and their parametrizations continuous.

**Root selection, including endpoints.** If a C1 function F on [a,b]
satisfies F(a)<=z<=F(b), it has a root F(r)=z with F'(r)>=0.
If F(a)=z and F'(a)>=0, use a. Otherwise start at a point with F<z and
take the first subsequent root. Its left difference quotients are
nonnegative. This also proves the claim at b; derivatives there are from
within the interval. A constant function causes no exception.

Apply this to
F(q)=(1-t)q-eX(1-q^2)/2 and L(p)=(1+t)p+eY(1-p^2)/2.
Their endpoint values bracket Y and X because the point belongs to K4.
We obtain p,q in [-1,1] with
$$
 Y=(1-t)q-eX(1-q^2)/2,\quad \rho=1-t+eXq\ge0,
$$
$$
 X=(1+t)p+eY(1-p^2)/2,\quad \sigma=1+t-eYp\ge0.                      \tag{7}
$$
Rearranging gives (5),(6). Zero radii already satisfy their caps. There is
no division by either radius, and no assumption of global monotonicity.

**Exact elimination.** Put D(r)=(1-r^2)/2 and
$$
 L=1+e^2G(p)G(q),\quad
 A=1+epq+e^2G(p)D(q),\quad B=1-epq+e^2G(q)D(p).
$$
The three exact relations
Y=rho*q-eXG(q), X=sigma*p+eYG(p), rho+sigma=2+e(Xq-Yp)
give
$$
 A\rho+B\sigma=2L.
                                                                         \tag{8}
$$
For clarity, the elimination first gives
X=(sigma*p+e*rho*q*G(p))/L and
Y=(rho*q-e*sigma*p*G(q))/L, which directly verify (8).
For 0<e<1, A,B>=1-e>0; for e=1 they remain nonnegative and A+B>=2.

Write Delta=p^2-q^2 and S=1+p^2+q^2. Direct expansion gives the certificate
$$
\begin{split}
 A C_e(q)+B C_e(p)-2L
={}&\frac{e^2}{2}\left(\Delta-\frac{epqS}{2}\right)^2\\
 &+e^4\left[G(p)G(q)(p^2D(p)+q^2D(q))
                 +\frac{9-p^2q^2S^2}{8}\right]\\
 &+\frac9{16}e^6\left[G(p)D(q)+G(q)D(p)\right]\ge0.                  \tag{9}
\end{split}
$$
Every term has a stated sign: D>=0, G>=1/2, p^2q^2<=1 and S<=3.
If both selected radii exceeded their caps, (8) would strictly exceed
its right side by (9). This is impossible, also at e=1 because at least
one weight is positive. Thus the continuous sweeps cover all of K4 for
0<e<=1. This strengthens the source's cubic padding criterion by retaining
the exact angular square before estimating the error.

**Theorem 2 (sharp constant in the stated cap family).** Among constant
quartic corrections C in 1+e^2*h(q)+C*e^4, the least C giving coverage
by both entire continuous sweeps for every sufficiently small positive e
is 9/16. This is not an optimality assertion over arbitrary profiles or
over finite cylinder covers.

For the lower bound, fix C<9/16 and choose p=1,
q=sqrt(1-3e/2). Let E=A*R(q)+B*R(p)-2L for this cap. Expansion of the
first equality underlying (9) gives E/e^4 -> 2C-9/8<0.
For sufficiently small e, delta=-E/(A+B)>0. Put
rho=R(q)+delta and sigma=R(p)+delta and define X,Y by the exact inverse
formulas after (8), and t=1-rho+eXq. Then (8) and both root equations
hold. Since p=1, X=1+t exactly. Also X,Y->1 and t->0. Thus X,Y>0,
|t|<1, and Y=(1-t)q-eX*D(q)<=1-t, proving membership in closed K4.
The cap is uniformly positive for small e even if the fixed C is negative.
Both root maps have positive derivatives on their whole intervals:
their minima are at least 1-t-e|X| and 1+t-e|Y|, which tend to 1.
Both roots are consequently unique, and both corresponding radii exceed
their caps. This is an actually uncovered point, not merely failure of a
sufficient estimate. Formula (9) proves attainability at C=9/16.

## 3. Finite triangles and exact area

For the equal partition use d=2/N, endpoints -1+jd and midpoint c_j.
Let M_j=max C_e on that interval. Since h is even and increasing in |q|,
M_j is the cap at the endpoint of greatest absolute value, including a
cell crossing zero. There is no numerical maximization.

In one canonical interval with midpoint c, let a=d/2, k=2e. Freezing (5)
at c gives, with b=q-c and s=eX,
$$
 u=\rho-sb,\qquad W=Y-cu=b\rho-sb^2/2,
 \quad |b|\le a, |s|\le k, 0\le\rho\le M.                         \tag{10}
$$
Define
$$
 z=ed/M,\quad \ell=a(1-z),\quad U=M+ed,
 \quad V=ed+\frac{ed^2}{4\ell}.                                    \tag{11}
$$
Since M>=1, e<=1/10 and d<=2, z<=1/5<1/2. The closed triangle is
$$
 T=\{(u,W):u\le U,\quad |W|\le\ell(u+V)\}.                         \tag{12}
$$
Its vertices are (-V,0),(U,±ell(U+V)), so it is compact and nondegenerate.

**Universal containment.** Each supporting functional of (12) is affine
in rho, so check rho=0 and rho=M. At rho=0, u>=-ka and |W|<=ka^2/2,
which imply W-ell*u<=ell*ka+ka^2/2=ell*V. At rho=M,
W=b(M+u)/2 and M-ka<=u<=M+ka. Since ell>=a/2 and M+u>0,
$$
 W-\ell u\le aM/2+(a/2-\ell)(M-ka)=\ell V.
$$
The last equality uses (a-ell)M=ka^2. Replacing (b,s,W) by
(-b,-s,-W) proves the other support inequality. Always u<=U.
This proves containment for every permitted parameter, including rho=0
and both angular endpoints.

The exact coordinate area and its useful upper bound are
$$
 A_j=\ell_j(U_j+V_j)^2
 =\frac{dM_j^2}{2}\left[1+4z_j+
       \frac{z_j^2(3/2-2z_j)^2}{1-z_j}\right]
 \le\frac d2(M_j+2ed)^2.                                            \tag{13}
$$
Indeed the bracket minus (1+2z)^2 is
z^2(4z^2-2z-7/4)/(1-z)<=0 on [0,1/2].

Under (4) and the angular relabeling q->-q, the physical lower intercept
vertices are (0,(cu+W)/2,Hu/2). The upper intercepts are their images
under (x,y,z)->(y,-x,H-z). Project them orthogonally onto the planes
perpendicular to the axes in Section 1. Projection is injective on each
intercept plane because the normal component of its axis is ±1.
It preserves the triangle type, compactness and nondegeneracy.

The canonical intercept area factor is H and the similarity contributes
1/4. Projection multiplies area by
g(c)=(1+e^2D_0(c))^(-1/2). Both families have identical areas. Therefore
$$
 \boxed{R_N(e)=\frac12\sum_{j=1}^N A_jg(c_j).}                       \tag{14}
$$
A point and its perpendicular projection differ along the cylinder axis;
projection does not alter the cylinder. Every angular root belongs to a
closed interval, with either choice valid at a common endpoint. Thus
(9),(10),(12) cover the entire closed K with exactly 2N labeled cylinders.
No claim that the frozen sides coincide is required: they enclose the
continuous sweeps and overlap sufficiently by (9).

## 4. Uniform mesh error

Put M_*=1+e^2+9e^4/16. On 0<e<=1/10,
$$
 M_*\le1+(81/80)e^2<1.011,\quad |h'|\le3,\quad |D_0'|\le6,
 \quad |g'|\le3e^2.                                                \tag{15}
$$
For q in a cell, M_j-C_e(q)<=3e^2d. A sharper integrated bound uses
sum_cell integral_cell(max_cell h-h)<=d*integral|h'|=2d, and
sum_cell integral_cell|q-c_j|=d/2. Comparing the unpadded maximum-cap sum
(1/4)sum d*M_j^2*g(c_j) with J(e) therefore gives the upper error
$$
 (M_*+3M_*^2/8)e^2d\le4e^2d.                                      \tag{16}
$$
Indeed M_j^2-C_e(q)^2<=2M_*e^2(max_cell h-h), and the weight
difference is at most 3e^2|q-c_j|. Multiply the integrals by 1/4.
Equation (13) adds at most
$$
 2M_*ed+2e^2d^2.                                                    \tag{17}
$$
For a lower bound, each frozen sweep contains its zero-free-coordinate
sector, of projected coordinate area g(c_j)*integral_cell C_e(q)^2/2.
The enclosing triangle therefore gives
$$
 R_N(e)\ge J(e)-(3M_*^2/8)e^2d.                                    \tag{18}
$$
Equations (16)–(18) imply |R_N-J|<=3ed=6e/N, since d<=2,e<=1/10.
They also give
$$
 R_N-J\le4e/N+8e^2/N+(81/20)e^3/N+8e^2/N^2.                        \tag{19}
$$
Replacing each cell width by the maximum delta in these same weighted
estimates proves the nonuniform mesh bound. Total angular length, not
the number of intervals, controls every summed error.

## 5. Uniform continuum remainder and the numerical constants

For t>=0, the alternating Taylor bounds give
1-t/2 <= (1+t)^(-1/2) <= 1-t/2+3t^2/8. Apply the upper bound to
t=e^2D_0(q) and expand the polynomial C_e(q)^2. Exact rational
integration gives
$$
 2J(e)=1-e^2/30+(929/630)e^4+O(e^6).
$$
The remainder can be bounded without an unspecified constant:
$$
 2J(e)\le1-e^2/30+(929/630)e^4+8e^6,
 \qquad 0<e\le1/10.                                                \tag{20}
$$
A coefficient-level derivation is in `research/cap-analysis.md`; the
independent verifier reconstructs the polynomial integral using fractions.
For an explicit elementary bound, put u=e^2, C=9/16, h<=1,D0<=3.
Multiplication of (1+2hu+(h^2+2C)u^2+2Chu^3+C^2u^4)
by (1-D0*u/2+3D0^2*u^2/8) leaves, above degree two, coefficients
at most 2C+27/4, C^2+27(1+2C)/8, 27C/4, and 27C^2/8,
respectively. Their weighted sum with u<=1/100 is less than 8.
The prefactor 1/2 and interval length 2 cancel in 2J.

Combining (19),(20) gives (2). Also (20) implies
J<=1/2-e^2/120 on this whole interval; the rational inequality is
1/60-(929/1260)/100-4/10000>1/120.
Using N>=1440/e in (1) proves the count bound.

At e=1/10,N=10000, the right side of (2) is exactly
$$
 \frac{157487232827}{315000000000}
 =0.499959469292\ldots <0.49996.                                    \tag{21}
$$
This is an upper bound, not a floating-point approximation to the true area.
The independent certificate additionally encloses the actual finite sum.

For N>=2/e^2, use the sharper (16),(17), with d<=e^2. After extracting
2e^3, the fourth-and-higher coefficient in (20)/2 plus the mesh error is
at most 929/1260+6e^2+M_*+(3/8)M_*^2+2e+(9/8)e^3.
It increases with e and is less than 5/2 at e=1/10, an exact rational
inequality checked independently. This proves (3).
At e<=1/125, 1/60-2e-(5/2)e^2>=19/37500, giving the stated saving.

## 6. Projection normalization and inequality dependencies

The outward face area vectors of K are (0,±H,-1),(±H,0,1).
Cauchy's elementary polytope projection formula gives, for a unit vector v,
$$
 A(v)=\max(H|v_x|,|v_z|)+\max(H|v_y|,|v_z|).
$$
Writing U=max(|v_x|,|v_z|/H), V=max(|v_y|,|v_z|/H), we have
(U+V)^2>=v_x^2+v_y^2+2v_z^2/H^2=1. Equality occurs at an x-axis
direction, proving A_min=H. The polytope formula follows by projecting
faces: almost every chord has two endpoints; projected edges have area zero.

| Inequality | Domain | Constant / dependency |
|---|---|---|
| Nonnegative selected radii (7) | closed K4, all e>0 | endpoint bracketing, first crossing |
| Exact overlap certificate (9) | p,q in [-1,1], 0<e<=1 | quartic coefficient 9/16 |
| Finite support enclosure (12) | 0<=rho<=M, s in [-2e,2e], z<=1/2 | exact affine supports |
| Triangle area bound (13) | 0<=z<=1/2 | convex quadratic endpoint bound |
| Derivative bounds (15) | q in [-1,1], e<=1/10 | 3,6,3e^2 |
| Mesh error (16)–(19) | e<=1/10, d<=2 | all sums weighted by cell length |
| Continuum remainder (20) | e<=1/10 | inverse-square-root Taylor inequality |
| Closed-body finite coverage | same as Theorem 1 | (7),(9),(12), nonsingular projection |

## 7. What source comparison is proved

The source's radial Appendix B common criterion requires, in its notation,
b_e(p)+b_e(q)>=9e for a cap 1+e^2(h+b_e). Taking p=q shows that every
cap certified by that criterion is pointwise at least
$$
 B_e(q)=1+e^2h(q)+(9/2)e^3.                                         \tag{22}
$$
This includes its optimal stated cubic constant 9/2. It also includes the
linear, fractional and square-root caps whenever their *effective* padding
satisfies this criterion. The existence of other proofs outside the
criterion is not ruled out.

For the equal midpoint partition used in (3), actual projected sweeps for
(22) are legitimate source bases and may be smaller than its displayed
triangles. Nevertheless, each contains the frozen projection of its
zero-free-coordinate sector. This gives the lower bound
$$
 R_{\rm source}\ge\frac14\sum_j g(c_j)\int_{I_j}B_e(q)^2\,dq
 \ge\frac12-\frac{e^2}{60}+\frac92 e^3-3e^4
 \quad(0<e\le1/100,\ d\le e^2).                                   \tag{23}
$$
To check the second inequality, use g>=1-e^2D0/2 and retain
1+2e^2h+9e^3 from B_e^2. The negative extra terms are at most
(3/2)e^4+(51/20)e^5, since integral hD0<=6 and integral D0=34/15.
Replacing g(q) by g(c_j) costs at most (3/4)B_*^2e^2d, where
B_*=1+e^2+(9/2)e^3<1.001. The total is less than 3e^4.
Larger caps and every source enclosure of their actual sweeps have at least
the same lower bound; no favorable displayed footprint is selected.

Subtracting (3) from (23) proves a strict same-count, identical-axis
improvement of at least 2e^3 throughout 0<e<=1/100. This comparison allows
arbitrary compact actual source bases as well as its enclosing polygons,
trapezoids and triangles, but fixes the midpoint partition as stated.

Angular Proposition 6.1 at tau=2e has the same count schedule and its stated
lower bound is 1/2-e^2/60+100e^3-32e^4. Equation (3) is strictly smaller
on this interval. Its secant axes differ from the midpoint radial axes by
the explicit horizontal slope correction -tau*d^2/16; this is the same
physical slope convention, not identical individual axes. Exact equality of
maximum angular deviation is a separate comparison and is not asserted here.

The following stronger comparisons were established after the user clarified
that the baseline is published constructions on their proved parameter ranges
and count conventions.

**Arbitrary published radial discretizations.** Every cap certified by the
source's common padding criterion has normalized cost

$$
R_{\rm radial}\ge\frac12-\frac1{23328000}>0.49999995
\tag{23a}
$$

whenever every finite axis has tangent of deviation at most sqrt(3)/10 from
its corresponding equality edge. This permits arbitrary tags, nonuniform
partitions, any finite count, and retuning the source tilt parameter. It is
an actual-cost lower bound for the projected sweeps and all their enclosing
bases, not a comparison against a selected source upper bound.

Here is the geometric reason. For a cell [l,r] and tag c, the frozen set
contains its zero-free-coordinate sector, plus two disjoint parallelogram
pieces outside its left and right sides. For every 1<=R(q)<=2, e<=1/8,
their projected extra area exceeds the possible tag-weight quadrature error:

$$
g_e(c)|S_I|\ge\frac12\int_I R(q)^2g_e(q)\,dq
 +\frac{29}{256}e[(c-l)^2+(r-c)^2].
\tag{23b}
$$

Thus summing arbitrary cells costs at least the continuum integral. For the
minimal old cap B_e, that integral is at least 1/2-e^2/60+4e^3 on e<=1/8,
whose global minimum is (23a). For larger source tilt e', the finite angle
budget itself gives g(c)>197/200, and the sector area gives
R>=(197/200)[1/2+(4/15)e'^2+(9/2)e'^3]>1/2 for e'>=1/8.
The full disjointness, endpoint, and constant calculations are in
`research/published-radial-angular-comparison.md`.

**Angular families.** Every maximum-cap family satisfying the source's
explicit coverage budget, and the whole stated angular cubic family, obeys

$$
R_{\rm angular}\ge\frac12-\frac1{93312000}.
\tag{23c}
$$

This follows from the exact area formula and convexity of the direction-weight
polynomial. It also holds for the stronger corollary obtained by retaining the
actual mesh in the old proof: eta>=7tau/8 suffices for this lower bound.
See research/published-proof-ranges.md, Section 3. It allows any permitted
count and is above both new 20000-cylinder certificates.

For every fixed positive-margin compatible angular family, there is also a
strict same-count comparison for all sufficiently small admissible tilt,
with the *actual finite maximum angle matched exactly*. If its count is
2N(tau), put e_*=T(tau)/sqrt(D_0(1-1/N)), where T is its actual maximum
axis tangent. The new uniform grid at e_* then has that angle and count.
The source's fixed margin gives a positive 2*eta*tau^2 cost gap; the new
finite loss is O(tau^3). The note supplies explicit comparison thresholds
in eta and the source's uniform constants, including its displayed secant
and node families. They must be intersected with the source's coverage range;
this asymptotic argument alone is not uniform as eta tends to zero.

A subsequent audit extracted the source's numerical coverage witness
(10+4E)tau<=eta<=1/480 and actual-area remainder (6E+2)tau^4. On that range
R>=1/2-1/5529600000, and its prescribed full list has at least 36864000
cylinders. Separate direct endpoint/squared certificates also exceed the
20000-cylinder budget. The full derivation and mappings are in
research/published-proof-ranges.md; this closes the earlier manuscript-only
comparison gap on the identified explicit published sufficient ranges.

The remaining comparisons with published ruled, nilpotent, rational, singular
and beam realizations are in `verification/published-generic-comparison.md`
and `research/published-slope-comparison.md`. They distinguish actual finite
counts and area from continuum guarantees. RESULT.md states the completed
published-range comparison and its limits; it does not treat an unspecified
larger validity range as a failure.

## 8. Obstruction to dominance over every generic source instance

There is a stronger logical limitation if "source construction" means every
admissible instance of the source's generic actual-projection method, including
instances whose cap admissibility is established by this new proof.
Apply that method to the very same new cap and the same partition and axes.
The resulting actual projected bases cover K and lie inside our triangles.
Their area is strictly smaller, not just bounded above by ours.

To see strictness, (10) gives u>=-ed for every actual intercept. But our
triangle extends down to u=-V, with V>ed. The subtriangle below u=-ed
has positive coordinate area ell*(V-ed)^2. Projection is nonsingular.
Consequently the normalized two-family area difference is at least
$$
 \frac12\sum_j g(c_j)\ell_j(V_j-ed)^2
 =\frac{e^2d^4}{32}\sum_j\frac{g(c_j)}{\ell_j}>0.                   \tag{24}
$$
These source-method instances need the new cap feasibility theorem, so (24)
does not refute the comparison with the source's already certified parameter
ranges in Section 7. It does rule out interpreting that bounded comparison
as strict dominance over all admissible instances of the generic projection
method. The permitted base class and meaning of "source construction" are
therefore essential parts of any broader comparison.

## 9. Exact enclosure optimality and a sharp finite-budget coefficient

The following result concerns the finite enclosure mechanism itself. It does
not assert optimality for the original variable-cap sweep, arbitrary triangles,
or arbitrary covers of K. Its class is larger than the source's fixed-opening
footprints: the opening slope is optimized as well as both intercepts.

**Theorem 3 (unique optimal symmetric enclosure).** Fix a,k,M>0 and
0<z=ka/M<=1/2. Let E consist of all points

$$
u=\rho-sb,\quad W=b\rho-sb^2/2,
\qquad |b|\le a,\quad |s|\le k,\quad 0\le\rho\le M.
$$

Among all triangles

$$
u\le U,\qquad |W|\le\ell(u+V),\qquad \ell>0,
$$

that contain E, the unique one of minimum coordinate area is

$$
\ell_0=a(1-z),\qquad U_0=M+ka,\qquad
V_0=ka+\frac{ka^2}{2\ell_0}.
\tag{25}
$$

Nonsingular projection multiplies every competing area by the same positive
factor, so the same uniqueness holds for perpendicular physical area.
Here symmetry means W->-W in the frozen intercept coordinates. Its projected
image need not be a Euclidean reflection symmetry in the perpendicular plane.

**Proof.** Write h=ell*V. Actual points of E force

$$
U\ge M+ka,\quad
h\ge ka\ell+\frac{ka^2}{2},\quad
h\ge M(a-\ell)+ka|\ell-a/2|.
\tag{26}
$$

The first is the maximum u coordinate; the second is attained at rho=0,
b=-a,s=-k; the last follows by taking rho=M,b=a and choosing the sign
of s. These are necessary inequalities for every triangle in the class,
independent of any sufficiency estimate. Its area is (ell*U+h)^2/ell,
which increases strictly with U and h on these positive lower bounds.

For ell>=ell_0>=a/2, the second bound yields

$$
F_0(\ell)=\ell\left(M+2ka+\frac{ka^2}{2\ell}\right)^2.
$$

Its derivative is positive for ell>=ell_0, because
ell_0>ka^2/[2(M+2ka)]. For a/2<=ell<=ell_0 the third bound yields

$$
F_1(\ell)=\frac{(aM-ka^2/2+2ka\ell)^2}{\ell}.
$$

Its derivative is negative throughout that interval: its stationary point
is (aM-ka^2/2)/(2ka), which is strictly larger than ell_0, since
1-(5/2)z+2z^2>0. For 0<ell<a/2, the absolute-value branch instead gives

$$
F_2(\ell)=\frac{(aM+ka^2/2)^2}{\ell},
$$

which strictly decreases up to a/2. The three lower bounds join at a/2
and ell_0. Thus every admissible triangle has at least F_0(ell_0) area,
with equality possible only at (25). The universal support proof in Section 3
establishes that this triangle actually contains E for z<=1/2. This proves
both attainability and uniqueness, including z=1/2.

**Theorem 4 (sharp finite-budget leading loss).** Fix 0<e<=1/10 and N>=1.
Allow every partition of [-1,1] into exactly N positive-width intervals.
On each interval freeze the axis at its midpoint and let M_j=max C_e on
that interval. In each of the two families, require the base triangle to
enclose the entire constant-M_j frozen set E above, with a=d_j/2,k=2e,
and permit any symmetric triangle in Theorem 3. Let F_N(e) be the infimum
of the resulting normalized total area over all such partitions and triangles.
All these 2N-cylinder constructions cover K by Section 2 and containment.
With M_*=1+e^2+9e^4/16 and g_min=(1+3e^2)^(-1/2),

$$
J(e)+\frac{4e}{N}\left[g_{\min}-\frac3{16}M_*^2e\right]
\le F_N(e)
\le J(e)+\frac{4e}{N}+\frac{8e^2}{N}
       +\frac{81e^3}{20N}+\frac{8e^2}{N^2}.
\tag{27}
$$

In particular, at N=ceil(2/e^2),

$$
F_N(e)=\frac12-\frac{e^2}{60}+2e^3+O(e^4)
=\frac12-\frac{\tau^2}{240}+\frac{\tau^3}{4}+O(\tau^4).
\tag{28}
$$

The cubic coefficient 2 (or 1/4 in physical tau) is therefore sharp over
this entire partition-and-enclosure class. This is a finite-budget lower
bound, not just separate optimality on a previously fixed partition.
More explicitly, on the whole interval 0<e<=1/10,

$$
\frac12-\frac{e^2}{60}+2e^3-\frac45e^4
\le F_{\lceil2/e^2\rceil}(e)
\le\frac12-\frac{e^2}{60}+2e^3+\frac52e^4.
\tag{29}
$$

**Proof.** Every cell has z=e*d_j/M_j<=1/5, so Theorem 3 applies. Its
exact minimum area, from (13), is at least d_j*M_j^2/2+2e*d_j^2*M_j.
Summing both families with the physical factors gives

$$
R\ge\frac14\sum_j d_j M_j^2g(c_j)
       +e\sum_j d_j^2 M_jg(c_j).
$$

Since M_j>=C_e(q) and |g'|<=3e^2, the first term is at least

$$
J(e)-\frac{3M_*^2e^2}{4}
          \sum_j\int_{I_j}|q-c_j|\,dq
=J(e)-\frac{3M_*^2e^2}{16}\sum_jd_j^2.
$$

The second is at least e*g_min*sum d_j^2. Their combined coefficient
is positive on e<=1/10. Cauchy's inequality gives sum d_j^2>=4/N,
proving the lower bound in (27). The uniform partition and (19) prove its
upper bound. Finally J(e)=1/2-e^2/60+O(e^4), and 4e/N=2e^3+O(e^5)
on the stated schedule, proving (28).

For (29), the positive lower projection polynomial gives
J(e)>=1/2-e^2/60+(1507/5040)e^4-(51/160)e^6>=1/2-e^2/60.
Also (3/16)M_*^2<1/5 and g_min>=1-3e^2/2. The ceiling gives
4e/N>=2e^3-e^5. Their product in (27) is at least
2e^3-(2/5)e^4-4e^5>=2e^3-(4/5)e^4. Equation (3) gives the upper bound.
The complete local and partition proofs are also collected in
`research/finite-triangle-optimality.md`.

Replacing the true cap by M_j enlarges each required frozen set. The theorem
does not transfer to enclosures required to contain only the original curved
cap, to asymmetric triangles, to independently sampled axes, or to arbitrary
compact bases. Any improvement of the cubic coefficient must leave at least
one of these declared conventions; the theorem does not claim that doing so
is impossible.
