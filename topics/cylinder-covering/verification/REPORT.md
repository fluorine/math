# Independent verification — 15 October 2026

The quartic cap, refined finite triangles, normalized cost bounds, and compact
generator pass independent algebraic verification. The comparisons include
global lower bounds for criterion-certified radial and angular families, and
count or angle obstructions for the published generic realizations. They do
not prove optimality among all cylinder covers or dominance over every
compatible cap. Each comparison's precise scope is stated below.

The subsequently verified compatible-secant construction is now stronger at
the same count and angle allowance. Its independent certificate, exact cost
intervals, and additional source-range comparison are in
[secant-report.md](secant-report.md). This report preserves the radial
construction and its separate local triangle optimality statement.

Run from the repository root:

```sh
python3 topics/cylinder-covering/verification/verify.py
```

The checker uses only Python's standard library, exact rational polynomial
arithmetic, binomial power sums, and integer square roots. It does not use
floating-point acceptance tests, sampled coverage, an installed computer algebra
system, or a numerical integration library. It reconstructs the sweep equations
and support inequalities independently. It imports `construction.py` only to
check the generator's returned vertices, directions, perpendicularity, and area.

## 1. Quartic cap: exact coverage certificate

Write

$$
G(r)=(1+r^2)/2,\quad D_-(r)=(1-r^2)/2,\quad H(r)=r^2G(r),
\quad C(r)=1+e^2H(r)+\frac9{16}e^4.
$$

For selected angular roots $p,q\in[-1,1]$, the underlying sweep equations are

$$
y=\rho q-exG(q),\qquad x=\sigma p+eyG(p),\qquad
\rho+\sigma=2+e(xq-yp).
$$

Set $T=1+e^2G(p)G(q)$. Elimination gives

$$
Tx=\sigma p+e\rho qG(p),\qquad
Ty=\rho q-e\sigma pG(q),
$$

and therefore

$$
A_q\rho+A_p\sigma=2T,
\quad A_q=1+epq+e^2G(p)D_-(q),
\quad A_p=1-epq+e^2G(q)D_-(p).
$$

For $0\le e\le1$, both weights are nonnegative and their sum is at least two.
Let $\Delta=p^2-q^2$ and $S=1+p^2+q^2$. The checker verifies the exact
polynomial identity

$$
\begin{aligned}
A_qC(q)+A_pC(p)-2T
={}&\frac{e^2}{2}\left(\Delta-\frac{epqS}{2}\right)^2\\
&+e^4\left[G(p)G(q)\{p^2D_-(p)+q^2D_-(q)\}
                  +\frac{9-p^2q^2S^2}{8}\right]\\
&+\frac9{16}e^6\{G(p)D_-(q)+G(q)D_-(p)\}.
\end{aligned}
$$

Every term is nonnegative. For the only less immediate term, the checker also
verifies

$$
9-p^2q^2S^2
=9\{(1-p^2)+p^2(1-q^2)\}
 +p^2q^2\{(1-p^2)+(1-q^2)\}(3+S).
$$

Consequently simultaneous strict failures $\rho>C(q),\sigma>C(p)$ contradict
the weighted balance, including at $e=1$ where an individual weight can
vanish. The first-crossing root lemma in the pinned radial source supplies
nonnegative radii on the entire closed tetrahedron. It uses no division by a
radius and includes zero-radius and boundary cases. Thus this certificate
proves full closed coverage for $0<e\le1$, independently of mesh refinement.

## 2. Refined triangle: universal support proof

For an interval of length $d=2a$, put $k=2e$, let $M$ be its maximum cap,
and write the frozen intercept as

$$
u=\rho-s\delta,\qquad W=\delta\rho-s\delta^2/2,
\quad |\delta|\le a,\quad |s|\le k,\quad0\le\rho\le M.
$$

If $z=ka/M\le1/2$, set

$$
\ell=a(1-z),\qquad U=M+ka,\qquad V=ka+\frac{ka^2}{2\ell}.
$$

All intercepts lie in $u\le U,\ |W|\le\ell(u+V)$.
Indeed each supporting functional is affine in $\rho$. At $\rho=0$, its
upper bound is $k\ell a+ka^2/2=\ell V$. At $\rho=M$, use
$W=\delta(M+u)/2$, $u\ge M-ka$, and $\ell\ge a/2$:

$$
W-\ell u
\le(a-\ell)M+\ell ka-ka^2/2
=\ell ka+ka^2/2.
$$

The last identity uses $(a-\ell)M=ka^2$. Reflection proves the other support
inequality. This proof holds for every allowed parameter, including interval
endpoints and $\rho=0$. It is not an endpoint-only coverage test.

The exact coordinate area is

$$
\ell(U+V)^2
=\frac{dM^2}{2}\left[1+4z+
                 \frac{z^2(3/2-2z)^2}{1-z}\right]
\le\frac d2(M+2ed)^2.
$$

The checker verifies both the area identity and
$4(1-z)-(3/2-2z)^2=7/4+2z(1-2z)\ge0$.
Since $M\ge1$, $e\le1/10$, and $d\le2$, the hypothesis holds for every
positive integer $N$, including $N=1$.

The earlier triangle with slope $a$, bottom $-3ed/2$, and top $M+ed$
is an immediate completion of the source's midpoint affine trapezoid
$(A,B)=(e,3e/4)$. Its validity is useful, but it is not an independent novelty
claim. Section 7 proves a minimum-area statement for the refined triangle in
the explicitly specified constant-cap, coordinate-reflection symmetric class.
The pinned formal companion's `Physical/FootprintRate.lean` already contains
explicit generic $O(1/N)$ estimates (`absolute_equal_mesh_error` and
`affine_equal_mesh_error`). Effectiveness of a footprint rate alone is therefore
also prior art. This checker is an exact algebra certificate, not a Lean kernel
verification of the new theorem.

## 3. Normalization and generator checks

For $K=\{(x,y,\sqrt2s):0\le s\le1, |x|\le1-s, |y|\le s\}$, the minimum
projection area is $\sqrt2$. The generator uses coordinates
$(x,y,z/\sqrt2)$, hence metric $\operatorname{diag}(1,1,2)$.
It returns the two axes

$$
(1,eG(c),ec),\qquad(-eG(c),1,ec)
$$

in those scaled coordinates. Their physical squared lengths are
$1+e^2D_0(c)$, where $D_0=G^2+2c^2$.
The physical tilt convention of the angular source is $\tau=2e$.
Projection is explicitly perpendicular in this metric.

The checker independently compares 36 representative outputs, covering
$e=1/100,1/10$, $N=1,2,3,10000$, both families, outer intervals and central
intervals. It checks exact intercept vertices, axes, cap maxima, perpendicular
vertices, parallel displacement under projection, positivity of the Gram
determinant, and the complete perpendicular area. The computed triangle area
squared divided by $A_{\min}^2$ is the Gram determinant divided by eight.
These checks validate generator output conventions; the universal proof above
is what certifies all cylinders and all body points.

With $d=2/N$, $M_j=C(|c_j|+d/2)$, and $z_j=ed/M_j$, the exact normalized
two-family cost is

$$
R_{e,N}=\frac d4\sum_{j=1}^N
\frac{M_j^2\left[1+4z_j+z_j^2(3/2-2z_j)^2/(1-z_j)\right]}
     {\sqrt{1+e^2D_0(c_j)}}.
$$

## 4. Uniform finite error and explicit saving

Let $Q(e)=\frac12\int_{-1}^1C(q)^2(1+e^2D_0(q))^{-1/2}\,dq$ and
$M_*=1+e^2+9e^4/16$. The independent integral calculation gives

$$
Q(e)\le1-\frac{e^2}{30}+\frac{929}{630}e^4+8e^6,
\qquad0<e\le1/10.
$$

The coefficient is checked by rational polynomial integration. For the
remainder, use the global Taylor upper bound
$(1+x)^{-1/2}\le1-x/2+3x^2/8$, then multiply by the exact cap square.
Dropping negative coefficients at orders at least $e^6$, using
$0\le H\le1$, $0\le D_0\le3$, and $e^2\le1/100$, bounds the resulting
coefficient of $e^6$ by less than eight. The checker verifies this rational
inequality rather than fitting a remainder from data.

An independent finite-error upper bound is

$$
R_{e,N}-\frac{Q(e)}2
\le 2M_*ed+\left(M_*+\frac38M_*^2\right)e^2d+2e^2d^2.
\tag{1}
$$

For the cap-maximum term, use
$\sum_I\int_I(\max_IH-H)\le d\int_{-1}^1|H'|=2d$.
For the frozen weight use $|g'|\le3e^2$ and
$\sum_I\int_I|q-c_I|=d/2$.
Finally the triangle area bound adds at most $2M_*ed+2e^2d^2$.
The zero-free-coordinate sector supplies the complementary lower error
$R_{e,N}-Q(e)/2\ge-3M_*^2e^2d/8$. Thus

$$
\left|R_{e,N}-Q(e)/2\right|\le6e/N
\quad(0<e\le1/10,\ N\ge1).
$$

Using $M_*\le1+(81/80)e^2$ and
$M_*+3M_*^2/8\le4$, (1) also proves the convenient theorem bound

$$
R_{e,N}\le\frac12-\frac{e^2}{60}+\frac{929}{1260}e^4+4e^6
 +\frac{4e}{N}+\frac{8e^2}{N}+\frac{81e^3}{20N}
 +\frac{8e^2}{N^2}.
\tag{2}
$$

If $N\ge\lceil2/e^2\rceil$, so $d\le e^2$, the sharper (1) implies

$$
R_{e,N}\le\frac12-\frac{e^2}{60}+2e^3+\frac52e^4
\quad(0<e\le1/10).
\tag{3}
$$

On $e\le1/100$ the quartic constant can be replaced by $9/4$.
In particular (3) proves
$R_{e,N}\le1/2-(19/37500)e^2<1/2$ for $0<e\le1/125$.
This is an explicit saving interval; coverage has the much larger interval
already stated. The original $5e^3/2$ target is therefore improved to
$2e^3$ for this footprint. Section 7 gives its sharp asymptotic coefficient
and the limits of that optimality statement.

## 5. Finite exact numerical certificates, with no large sums

Write $f(z)=(3/2-2z)^2/(1-z)$. It is decreasing on $[0,1/2]$, as certified
by its derivative numerator $-15/4+8z-4z^2\le-3/4$. Therefore the exact area
bracket is bounded by

$$
M_j^2+4edM_j+(ed)^2f\left(\frac{ed}{1+9e^4/16}\right)
\quad\text{and}\quad
M_j^2+4edM_j+(ed)^2f\left(\frac{ed}{1+e^2+9e^4/16}\right).
$$

Both are polynomials in the cell index with rational coefficients. Multiply
them respectively by the degree-seven lower and degree-six upper Taylor
polynomials of $(1+x)^{-1/2}$, with $x=e^2D_0(c_j)$.
Taylor's integral remainder has the required sign for every $x\ge0$.
Exact binomial power sums then enclose all $N$ terms without iterating over
them. Odd $N$ uses one separate central cell. The power-sum recurrence is
checked against small direct integer sums; independent integer-square-root
enclosures check the complete sums for $N=1,2,3,7$.

The displayed decimal endpoints below are rounded outward from exact rationals:

| Canonical tilt $e$ | Intervals $N$ | Cylinders | Certified actual $R_{e,N}$ interval |
|---|---:|---:|---|
| $1/10$ | 10,000 | 20,000 | [0.499947504745824, 0.499947504745984] |
| $1/100$ | 20,000 | 40,000 | [0.500000345647165, 0.500000345647166] |
| $1/1000$ | 2,000,000 | 4,000,000 | [0.499999985334570, 0.499999985334571] |

At $e=1/10,N=10000$, even the weaker general bound (2) is at most
**0.499959469292064**, strictly below $1/2-1/25000$.
The exact area enclosure is stronger still. At $e=1/100$, the proposed
schedule $N=\lceil2/e^2\rceil$ gives an area **above** one half; this is
negative evidence against claiming saving throughout $0<e\le1/100$ on that
schedule. No point-cloud or floating-point experiment overrides that result.

## 6. Verified comparison and its precise limits

The radial source's common sufficient padding criterion is
$b_e(p)+b_e(q)\ge9e$ for all $p,q$. Setting $p=q$ forces
$b_e(p)\ge9e/2$ pointwise. Every cap certified by this criterion therefore
dominates

$$
B(q)=1+e^2H(q)+\frac92e^3.
$$

This covers the best stated cubic member, all larger cubic members, and the
linear, fractional, or square-root members **when their effective padding
satisfies that same criterion at the chosen tilt**. It does not declare
smaller padding geometrically inadmissible.

For the same partition and midpoint tags, even an actual swept projection
contains the zero-free-coordinate sector. Thus its normalized total area, and
the area of any enclosing source footprint, is at least

$$
L_{e,N}=\frac14\sum_I
\frac{\int_I B(q)^2\,dq}{\sqrt{1+e^2D_0(c_I)}}.
\tag{4}
$$

The checker evaluates a rigorous lower bound on (4), again by exact power sums
and a Taylor polynomial of degree seven. The three rows above give respective
source lower bounds

$$
0.504347312079790,\qquad
0.500002834956276,\qquad
0.499999987833506.
$$

These exceed the corresponding new upper bounds; importantly, the comparison
is not confined to the source's largest illustrated triangles.

A uniform analytic comparison is also certified. Using
$(1+x)^{-1/2}\ge1-x/2$, the continuum lower polynomial has coefficients
$-17/90,-27/20$ at $e^4,e^5$, a positive coefficient at $e^6$, and
$-83/70,-459/80$ at $e^7,e^8$. The freezing error is at most
$3(1+e^2+9e^3/2)^2e^2d/8$. Hence, for $d\le e^2$ and $0<e\le1/10$,

$$
L_{e,N}\ge\frac12-\frac{e^2}{60}+\frac92e^3-\frac34e^4.
$$

Combining this with (3) yields the positive gap
$L_{e,N}-R_{e,N}\ge(5/2)e^3-(13/4)e^4>0$.

There is one further exact angular-source comparison at the explicit successful
instance $e=1/10$, hence physical $\tau=1/5$. The quantitative coverage
corollary for uniform secant, maximum-cap triangles requires its sufficient
budget

$$
2\eta-(2+2\eta)\tau-\tau^2/4\ge0.
$$

At $\tau=1/5$, satisfying this budget requires $\eta\ge41/160$, whence
every cutoff $T_j\ge2041/4000$. The source directions obey
$0\le\alpha_j\le1/2$, $|\beta_j|\le1/2$, so
$\alpha_j^2+2\beta_j^2\le3/4$. Its exact area formula and
$\sqrt{1+x}\le1+x/2$ therefore give

$$
R_{\mathrm{angular}}\ge
\frac{2(2041/4000)^2}{1+3\tau^2/8}
=\frac{4165681}{8120000}>\frac12.
$$

This includes every margin certified by that explicit budget, including the
larger cubic margin used in Proposition 6.1, for any uniform mesh satisfying the
corollary's mesh condition. It uses the exact area formula; it does not apply
the separate area Taylor corollary outside its $\eta\le1/8$ hypothesis. The
budget is sufficient, not a necessary geometric coverage condition. This
comparison does not settle feasibility of the other compatible caps.

The arbitrary-partition, arbitrary-tag and independently optimized radial-tilt
comparison requires the additional argument in section 8; it does not follow
from (4) alone. Section 9 separately handles the published generic recipes and
beam axes, without using missing convergence constants as lower bounds.

The angular compatible-boundary theorem also allows fixed positive margins,
other caps and sampling conventions. The initial manuscript-only audit left
its precise sufficiently-small range unresolved. The subsequently pinned
formal threshold closes that comparison on the published proved range; see
section 6 of [secant-report.md](secant-report.md). The continuous-cap candidate
with cheaper area at the same numerical tilt and count is now covered by the
new secant argument in that report. Its earlier area calculation alone did
not establish coverage, and the new proof does not make the source's old
sufficient threshold a necessary geometric condition.

## 7. Local triangle optimum and the sharp count-dependent term

These statements concern the full constant-cap comparison set
$S_M=\{(u,W):u=\rho-s\delta,\ W=\delta\rho-s\delta^2/2,\
|\delta|\le a,|s|\le k,0\le\rho\le M\}$, where
$0<z=ka/M\le1/2$. They need not apply to the smaller set obtained by
using the actual variable cap on an interval.

Normalize coordinates by $(u,W)\mapsto(u/M,W/(aM))$. The upper vertices
of its convex hull are

$$
(-z,z/2),\quad(1-z,1-z/2),\quad(1+z,1+z/2),
$$

with their reflections in (W=0) forming the lower boundary. To see that these
give the whole hull, the (
ho=0) set lies in its four-vertex rectangle,
the (
ho=M) set lies in its endpoint trapezoid, and every intermediate
point is on a segment between these endpoint sets. All their extreme vertices
are realized by (delta=\pm a,s=\pm k). The two extra rectangle vertices
are below the displayed upper/lower supports when (z\le1/2). Its normalized
area, checked directly from these vertices, is (1+4z).

Consider all nondegenerate triangles invariant under the **coordinate**
reflection (W\mapsto-W). For a triangle with right vertical base and side
slope (l>0), the best base position is (u=1+z). Its supporting intercept is

$$
h(l)=\max_{S_M}(W-lu).
$$

For (l\ge1/2), the vertices give

$$
h(l)=\max\{z(l+1/2),\ 1-l+z(l-1/2)\}.
$$

The switch occurs at (l_0=1-z). The area is

$$
\frac{[l(1+z)+h(l)]^2}{l}.
$$

On (1/2\le l\le l_0), it equals

$$
\frac{(1-z/2+2zl)^2}{l}
$$

and decreases strictly. Its derivative has sign
$(2zl)^2-(1-z/2)^2<0$, because

$$
1-z/2-2z(1-z)=2(z-5/8)^2+7/32>0.
$$

On (l\ge l_0) the area is
$[l(1+2z)+z/2]^2/l$, whose derivative is positive. For (l<1/2), the
rightmost upper corner alone gives area at least $(1+z/2)^2/l$, exceeding
the (l=1/2) value. Thus the refined triangle is the unique minimizer among
these right-base triangles.

A reflection-symmetric triangle facing the other way has base position
(A\le-z) and apex position (B>1+z). Containing the two rightmost corners
forces area at least

$$
(1+z/2)\frac{(B-A)^2}{B-(1+z)}
\ge4(1+z/2)(1+2z)>(1+2z)^2.
$$

The last expression already bounds the refined triangle's area from above.
This excludes the other orientation and completes the local symmetric-triangle
minimum proof. It does not exclude asymmetric triangles, different sweep
partitions, or variable-cap footprint improvements. A linear perpendicular
projection preserves area comparisons but need not turn this coordinate
reflection into ordinary Euclidean reflection in the perpendicular plane.

Now let an arbitrary partition have (N) intervals of lengths (d_i), midpoint
tags, and the corresponding refined constant-cap triangles. Write

$$
J(e)=Q(e)/2,\quad M_*=1+e^2+9e^4/16,\quad
g_{\min}=(1+3e^2)^{-1/2}.
$$

The exact area formula contributes at least
(e\sum_i d_i^2M_i g_e(c_i)\ge e g_{\min}\sum_i d_i^2) beyond the
cap-square term. Replacing each cap maximum by the actual cap can only lower
that term; freezing its weight loses at most

$$
\frac14 M_*^2(3e^2)\sum_i\int_{I_i}|q-c_i|\,dq
=\frac3{16}M_*^2e^2\sum_i d_i^2.
$$

The resulting coefficient is positive for (e\le1/10). Cauchy's inequality
$\sum_i d_i^2\ge4/N$ proves

$$
R_{e,N}\ge J(e)+\frac{4e}{N}
\left[(1+3e^2)^{-1/2}-\frac3{16}M_*^2e\right].
\tag{5}
$$

For uniform grids, the existing upper bound (1) and (5) yield the explicitly
uniform estimate

$$
\left|\frac{R_{e,N}-J(e)}{4e/N}-1\right|\le3e,
\qquad 0<e\le1/10,\quad N\ge1.
\tag{6}
$$

The rational endpoint inequalities for (5)--(6) are checked independently.
Also, using (C^2\ge1+2e^2H) and (g_e\ge1-e^2D_0/2),

$$
J(e)\ge\frac12-\frac{e^2}{60}-\frac{83}{315}e^4.
$$

Together with the already verified upper bound, this proves
$J(e)=1/2-e^2/60+O(e^4)$. Therefore at
$N=\lceil2/e^2\rceil$,

$$
R_{e,N}=\frac12-\frac{e^2}{60}+2e^3+O(e^4).
$$

The coefficient (2) is attained by the uniform grid and cannot be reduced
by another midpoint partition with the same count using these constant-cap
symmetric triangles. It is not an optimality theorem for all triangular
cylinders or all covers.

## 8. Independently verified global radial and angular floors

The [full comparison proof](../research/published-radial-angular-comparison.md)
extends the radial result beyond identical partitions. Its key geometric
step is independently checked here. In any interval (I=[l,r]) tagged at
(c\in I), the actual frozen intercept set contains its zero-free-coordinate
sector and two disjoint endpoint pieces outside the sector. The left piece
uses (q=l,-2e\le s\le0,2e(c-l)\le\rho\le R(l)), and the right piece is
its counterpart at (q=r). Their Jacobians are respectively
$(c-l)^2/2$ and $(r-c)^2/2$.

For (e\le1/8) and (1\le R\le2), their extra projected area exceeds the
tag-freezing error, leaving the positive coefficient

$$
\frac{125}{128}\cdot\frac12-\frac38=\frac{29}{256}.
$$

Consequently every such actual-base cover, with arbitrary tags and finite
partitions, has ratio at least $\frac14\int R^2g_e$. Larger certified
caps contain the same comparison pieces for
$B_e=1+e^2H+9e^3/2$, so this applies even when the source cap itself
exceeds two.

For (e\le1/8), exact integral coefficients and positive Taylor lower factors
then give

$$
J_B(e)\ge\frac12-\frac{e^2}{60}+\frac92e^3
-\frac32e^4-\frac{51}{20}e^5
\ge\frac12-\frac{e^2}{60}+4e^3.
$$

For larger source tilt, the actual finite angle budget
$\tan\Theta\le\sqrt3/10$ ensures all tag projection factors exceed
(197/200). The sector alone gives

$$
R\ge\frac{197}{200}
\left(\frac12+\frac4{15}e^2+\frac92e^3\right)
\ge\frac{1552163}{3072000}>\frac12\qquad(e\ge1/8).
$$

Thus independently choosing the source tilt, tags, count and partitions cannot
beat the following floor **within the common-padding criterion**:

$$
\boxed{R_{\rm radial}\ge\frac12-\frac1{23328000}.}
\tag{7}
$$

For the angular maximum-cap construction, put
(A(q)=D_0(q)/4) and (d(q)=H(q)/8). On every secant interval its coefficient
(A_j\le A(c_j)), and (A) is convex, so
$\sum |I_j|A_j\le\int A=17/30$. Also
$\int d=1/15$ and $A_j\le3/4$. The exact area formula implies

$$
R_{\rm angular}\ge\frac12-\frac{\tau^2}{240}
+\eta\tau^2(2-3\tau^2/4)-\frac{\tau^4}{40}.
$$

The explicit sufficient coverage budget forces
$\eta\ge\tau/(1-\tau)\ge\tau$, (0<\tau<1). Hence

$$
R_{\rm angular}\ge\frac12-\frac{\tau^2}{240}+\tau^3
\ge\boxed{\frac12-\frac1{93312000}.}
\tag{8}
$$

The checker reconstructs the secant coefficient inequality and both continuum
coefficients, and verifies the nonnegative factorizations

$$
4x^3-x^2/60+1/23328000=4(x-1/360)^2(x+1/720),
$$

$$
x^3-x^2/240+1/93312000=(x-1/360)^2(x+1/720).
$$

These establish global minima, not sampled minimizations. The angular floor
uses its explicit budget's stated coverage hypotheses; it is not a necessary
coverage condition for every compatible cap. The published cubic's remaining
tilt range is handled directly by its larger cap, as in the comparison note.
Both floors exceed the new fixed-instance upper certificate.

## 9. Published generic recipes: checks and limitations

The [independent generic comparison](published-generic-comparison.md) gives the
full geometry, normalization, source locations and count conventions. The
checker verifies its rational constants and reconstructs the rational field's
derivative determinant and field-norm inequalities.

At the common finite axis allowance $\arctan(\sqrt3/10)$:

- Published beam-strip axes exceed the allowance, including relative to every
  tetrahedron edge direction.
- The prescribed square-zero apex lists contain more than
  (102400/3) cylinders, before the retained grids are added.
- The full square-grid recipes for rational and singular fields have actual
  ratio at least (637/1250) if their total count is at most 20,000. This uses
  the mandatory retained collar and accommodates physical domain scaling.
- The rational product/logarithmic constructions, with their published
  saving-error allocations, need more than 20 million selected main cells in
  one family. The argument survives finite subcover selection and only assumes
  the angle bound on the selected finite axes.

These are bounds for the specified recipes, not for optimized replacement
apex nets, pruned grids, different mesh relations, or every possible generic
theorem instance. The product/logarithmic proof does not settle the entire
unbounded-count tail of the small-(e) schedule. No universal all-baseline
dominance, global cylinder optimum, or literature-novelty claim is certified.
