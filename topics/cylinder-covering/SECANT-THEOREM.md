# A quartic overlap theorem with effective finite secant covers

Manuscript, 15 October 2026. This theorem reuses the exact secant axes and
angular-side matching of the published angular construction. Its new input is
the quartic simultaneous-failure certificate and an explicit perturbation
bound for finite secants. The resulting theorem changes the proved cap margin
and parameter range; it is not a claim that secant sectors themselves are a
new geometric family.

For the edge-two regular tetrahedron, the construction below gives exactly
2N compact triangular cylinders, a closed-body coverage proof, a uniform
finite error at most 2e/N, and an independently certified 20000-cylinder
example with normalized total area

$$
0.499921585997001674\le R\le0.499921585997001774<0.499922.
$$

On the source count schedule N=ceil(2/e^2), its actual cubic coefficient is
1/2 in canonical e units, or 1/16 in physical tau=2e units. The earlier
full-sweep frozen triangle remains valid and has sharp cubic coefficient 2
within its declared enclosure class. The present triangles do not enclose
each cell's entire continuously tilted sweep, so that lower bound does not
apply. See [THEOREM.md](THEOREM.md), Theorems 3–4.

## 1. Explicit triangles, axes, and exact cost

Put $H=\sqrt2$ and
$$
 K=\{(x,y,Hs):0\le s\le1,\ |x|\le1-s,\ |y|\le s\},
 \qquad A_{\min}(K)=H.
$$
All areas are divided by $H$. Define
$$
 G(q)=\frac{1+q^2}{2},\quad D(q)=\frac{1-q^2}{2},\quad
 h(q)=q^2G(q),\quad D_0(q)=G(q)^2+2q^2,
$$
$$
 C_e(q)=1+e^2h(q)+\frac9{16}e^4,\qquad
 M_*=1+e^2+\frac9{16}e^4.
$$
Take any partition into $N$ positive-width closed intervals
$I_i=[l_i,r_i]$, with disjoint interiors and union $[-1,1]$. Write
$$
 d_i=r_i-l_i,\qquad a_i=d_i/2,\qquad c_i=(l_i+r_i)/2,
 \qquad A_i=\frac{1+l_ir_i}{2}=G(c_i)-\frac{a_i^2}{2}.
$$
For $0<e<1$, put
$$
 K_0=M_*(e+e^2/2)+2e^2,\qquad
 \delta_i=\frac{K_0a_i+(M_*e^2/2)a_i^2}{1-e},                 \tag{1}
$$
$$
 M_i=\max_{q\in I_i}C_e(q)+\delta_i.                         \tag{2}
$$
The maximum is attained at the endpoint of largest absolute value,
since $h$ is even and increases with $|q|$.

Use the lower and upper intercept triangles
$$
 P_i=\{(0,qt,Ht):q\in I_i,\ 0\le t\le M_i/2\},
$$
$$
 Q_i=\{(pt,0,H(1-t)):p\in I_i,\ 0\le t\le M_i/2\}
$$
with respective axes
$$
 v_i=(1,eA_i,Hec_i),\qquad w_i=(-eA_i,1,Hec_i).              \tag{3}
$$
Their orthogonal projections onto $v_i^\perp,w_i^\perp$ are the actual
bases. Projection preserves each cylinder and is injective on its intercept
plane, since the normal component of the axis equals $1$. The bases are
therefore compact nondegenerate triangles.

**Coverage theorem.** For every $0<e<1$, the $2N$ labeled cylinders just
defined cover every point of the closed $K$. More generally, the same proof
allows a continuous or measurable sector cap $R_i(q)$ whenever
$R_i(q)\ge C_e(q)+\delta_i$, with the corresponding compactness hypotheses
if compact bases are required.

The exact normalized area of the triangular version is
$$
 \boxed{\displaystyle
 R_{\rm sec}(e;\mathcal P)=\frac14\sum_i
       \frac{d_iM_i^2}{\sqrt{1+e^2(A_i^2+2c_i^2)}}.}         \tag{4}
$$
Indeed each intercept triangle has area $Hd_iM_i^2/8$, projection
multiplies this by the displayed inverse square root, and there are two
families.

For the equal grid, $d=2/N$, all padding values are the same:
$$
 \boxed{\displaystyle
 \delta(e,d)=
 \frac{d\{M_*(e+e^2/2)+2e^2+M_*e^2d/4\}}{2(1-e)}.}          \tag{5}
$$
The source's physical angular parameter is $\tau=2e$, with its
$\alpha_i=A_i/2,\ \beta_i=c_i/2$. Thus (3) are precisely its secant axes.
For the equal grid the largest physical deviation angle has tangent
$$
 \boxed{\sqrt3\,e(1-1/N).}                                  \tag{6}
$$
To see this, $A_i^2+2c_i^2$ increases with $|c_i|$, and the two outer
cells have $A_i=|c_i|=1-1/N$. Formula (6) also holds for $N=1$, when
the deviation is zero.

## 2. Closed-body angular selection

The needed first-crossing argument is the one in the source
[coverage proof](sources/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/build/sections/coverage.tex).
It works for every positive-width partition and needs no monotonicity.

For $q\in I_i$, define $L_i(q)=A_i-qc_i$. At either endpoint,
$$
 L_i(q)=D(q).
$$
Consequently the sector boundaries agree between neighboring cells.
Also $L_i$ is the linear interpolation of the two nonnegative endpoint
values of $D$, so $L_i(q)\ge0$.

Fix any $(x,y,Hs)\in K$. At each partition node $q_k$, set
$$
 F_k=sq_k+exD(q_k).
$$
Its endpoints are $F_0=-s\le y\le s=F_N$.
Choose the first $k\ge1$ with $F_k\ge y$. Then
$F_{k-1}\le y\le F_k$, including the case $y=F_0$; denote the chosen
cell by $I_i$. Put
$$
 t_0=s-exc_i,\qquad y_0=y-exA_i.
$$
The two endpoint inequalities are exactly
$$
 l_it_0\le y_0\le r_it_0.
$$
Subtracting the outer expressions gives $d_it_0\ge0$, hence $t_0\ge0$.

For the upper family, apply the same argument to
$$
 E_k=(1-s)q_k-eyD(q_k),\qquad E_0=-(1-s)\le x\le1-s=E_N.
$$
It selects a cell $I_j$ such that
$$
 s_0=1-s+eyc_j\ge0,\quad x_0=x+eyA_j,\quad
 l_js_0\le x_0\le r_js_0.
$$

If either selected radius vanishes, its intercept is the triangle's tip
and that cylinder already covers the point. Otherwise let
$$
 \rho=2t_0,\quad \sigma=2s_0,\quad
 q=y_0/t_0\in I_i,\quad p=x_0/s_0\in I_j,\quad X=2x,\quad Y=2y.
$$
The exact relations are
$$
 Y=\rho q+eXA_i,\qquad X=\sigma p-eYA_j,\qquad
 \rho+\sigma=2+e(Yc_j-Xc_i).                                 \tag{7}
$$
Every choice used non-strict inequalities, so it includes angular nodes,
all faces and edges, and all four vertices. Division occurred only after
the zero-radius cases were already covered.

## 3. Exact discrete and continuous certificates

Let $\Lambda=1+e^2A_iA_j$. Solving the first two equations of (7) gives
$$
 X=\frac{\sigma p-e\rho qA_j}{\Lambda},\qquad
 Y=\frac{\rho q+e\sigma pA_i}{\Lambda}.
$$
Substitution into the third equation yields
$$
 w_\rho\rho+w_\sigma\sigma=2\Lambda,                          \tag{8}
$$
where
$$
 w_\rho=1-eqc_j+e^2A_j(A_i-qc_i),\qquad
 w_\sigma=1+epc_i+e^2A_i(A_j-pc_j).                          \tag{9}
$$
Here $0\le A_i\le1$, $L_i\ge0$, so
$$
 w_\rho,w_\sigma\ge1-e>0.                                   \tag{10}
$$

For comparison at the same $p,q$, write
$$
 N_0=1+e^2G(p)G(q),\quad
 A_-=1-epq+e^2G(p)D(q),\quad
 B_+=1+epq+e^2G(q)D(p).
$$
The continuous certificate, expressed in these physical coordinates, is
$$
\begin{split}
 A_-C_e(q)+B_+C_e(p)-2N_0
 ={}&\frac{e^2}{2}\left[p^2-q^2+
       \frac{epq(1+p^2+q^2)}2\right]^2\\
 &+e^4\left[
 G(p)G(q)\{p^2D(p)+q^2D(q)\}
 +\frac{9-p^2q^2(1+p^2+q^2)^2}{8}\right]\\
 &+\frac9{16}e^6\{G(p)D(q)+G(q)D(p)\}\ge0.                  \tag{11}
\end{split}
$$
The signs of the two linear terms in (9) are reversed from the canonical
$K_4$ convention in the existing manuscript. Accordingly the square in
(11) has a plus sign. This is the same certificate after reflecting the
lower angular parameter; no inequality changes. Nonnegativity follows
from $D\ge0$, $|p|,|q|\le1$, and $1+p^2+q^2\le3$.

To bound the change from (11) to (8), write $b=q-c_i$ and
$$
 E_i(q)=\frac{a_i^2-b^2}{2}.
$$
Then
$$
 L_i(q)=D(q)-E_i(q),\quad 0\le E_i(q)\le a_i^2/2,\quad
 |A_i-G(q)|\le a_i.                                        \tag{12}
$$
For the last inequality,
$$
 |A_i-G(q)|=\left|-c_ib-\frac{a_i^2+b^2}{2}\right|
 \le |c_i|a_i+a_i^2\le a_i,
$$
since $|c_i|+a_i\le1$. The same estimates hold in $I_j$.

Using $D\le1/2$, $G,A_i,A_j\le1$, one obtains
$$
 |w_\rho-A_-|
 \le ea_j+\frac{e^2}{2}(a_j+a_i^2),\qquad
 |w_\sigma-B_+|
 \le ea_i+\frac{e^2}{2}(a_i+a_j^2),                          \tag{13}
$$
$$
 |\Lambda-N_0|\le e^2(a_i+a_j).                             \tag{14}
$$
For example,
$$
 A_jL_i(q)-G(p)D(q)
 =[A_j-G(p)]D(q)-A_jE_i(q),
$$
which proves the first second-order estimate in (13).

Because $C_e\le M_*$, equations (11)--(14) give
$$
 w_\rho C_e(q)+w_\sigma C_e(p)-2\Lambda
 \ge-K_0(a_i+a_j)-\frac{M_*e^2}{2}(a_i^2+a_j^2).             \tag{15}
$$
By (1) and (10),
$$
 w_\rho\delta_i+w_\sigma\delta_j
 \ge(1-e)(\delta_i+\delta_j)
 =K_0(a_i+a_j)+\frac{M_*e^2}{2}(a_i^2+a_j^2).
$$
Thus any caps at least $C_e(q)+\delta_i,C_e(p)+\delta_j$ satisfy
$$
 w_\rho R_i(q)+w_\sigma R_j(p)\ge2\Lambda.                   \tag{16}
$$
If both selected cylinders missed the point, their positive radii would
strictly exceed their caps. By (10), their weighted sum would be strictly
larger than (16), contradicting (8). This completes the coverage proof.

## 4. Uniform finite-area bounds

In this section $0<e\le1/10$. Let
$$
 J(e)=\frac14\int_{-1}^1 C_e(q)^2g(q)\,dq,\qquad
 g(q)=(1+e^2D_0(q))^{-1/2}.
$$
The continuous-cap calculation in
[cap-analysis.md](research/cap-analysis.md) gives
$$
 J(e)\le\frac12-\frac{e^2}{60}+\frac{929}{1260}e^4+4e^6,
 \qquad
 J(e)=\frac12-\frac{e^2}{60}+O(e^4).                         \tag{17}
$$
This follows from
$(1+z)^{-1/2}\le1-z/2+3z^2/8$ for $z\ge0$, exact polynomial
integration, and a remainder bound uniform for $e^2\le1/100$.

For an equal grid, let $\widehat M_i=\max_{I_i}C_e$ and
$$
 g_i^{\rm sec}=(1+e^2(A_i^2+2c_i^2))^{-1/2}.
$$
Then the following bound holds for every $N\ge1$:
$$
\boxed{\begin{split}
 R_{\rm sec}(e,N)\le J(e)
 &+\left(M_*+\frac38M_*^2\right)e^2d\\
 &+M_*\delta+\frac12\delta^2+\frac1{16}M_*^2e^2d^2,
 \qquad d=2/N,\quad \delta=\delta(e,d).
\end{split}}                                               \tag{18}
$$

Here are all discretization estimates used in (18).

First, $C_e$ has total variation $2e^2$, so
$$
 \sum_i\int_{I_i}(\widehat M_i-C_e(q))\,dq\le2e^2d.
$$
Multiplying by $\widehat M_i+C_e(q)\le2M_*$ and dividing by four
bounds the maximum-cap error by $M_*e^2d$.

Second, $|D_0'|\le6$, hence $|g'|\le3e^2$, and
$\sum_i\int_{I_i}|q-c_i|\,dq=d/2$. The midpoint-weight error,
after the factor $1/4$, is at most $3M_*^2e^2d/8$.

Third,
$$
 D_0(c_i)-(A_i^2+2c_i^2)
 =G(c_i)a_i^2-a_i^4/4\in[0,a_i^2].
$$
The derivative of $(1+e^2z)^{-1/2}$ in $z$ has magnitude at most
$e^2/2$. Thus
$$
 0\le g_i^{\rm sec}-g(c_i)\le e^2d^2/8,
$$
and the resulting normalized area error is at most
$M_*^2e^2d^2/16$.

Finally, adding the constant padding to all cells changes their normalized
area by
$$
 \frac14\sum_i d_i(2\widehat M_i\delta+\delta^2)g_i^{\rm sec}
 \le M_*\delta+\delta^2/2.
$$
These four estimates prove (18). They also imply the lower bound
$$
 R_{\rm sec}(e,N)\ge J(e)-\frac38M_*^2e^2d,                  \tag{19}
$$
since increasing the cap and replacing midpoint weights by secant weights
are both nonnegative changes.

A simple two-sided bound, useful independently of the count schedule, is
$$
 \boxed{|R_{\rm sec}(e,N)-J(e)|\le ed=2e/N.}                 \tag{20}
$$
Indeed $M_*<1011/1000,\ M_*^2<1023/1000$, and (5), $d\le2$, give
$\delta\le3ed/4$. In (18), use $e\le1/10,\ ed\le1/5$ and
$M_*+3M_*^2/8<7/5$. The entire upper error is at most
$$
 \left(\frac{3033}{4000}+\frac9{160}
       +\frac7{50}+\frac{1023}{80000}\right)ed
 =\frac{77383}{80000}ed<ed.
$$
The lower error in (19) is smaller still. For a nonuniform partition the
same proof, with $d=\max_i d_i$ and the local padding (1), gives
$$
 |R_{\rm sec}(e;\mathcal P)-J(e)|\le e\max_i d_i.            \tag{21}
$$
Use $\sum_i d_i^2\le2d$, $\sum_i d_i^3\le2d^2$ in the preceding
estimates.

A count bound valid throughout 0<e<=1/10 follows immediately. Equation (17)
gives J(e)<=1/2-e^2/120, because
929/(1260*100)+4/10000<1/120. Consequently

$$
N\ge\lceil480/e\rceil
\quad\Longrightarrow\quad
R_{\rm sec}(e,N)\le\frac12-\frac{e^2}{240}.                \tag{21a}
$$

Equivalently, a mesh at most e/240 suffices. The indexed generator uses
constant storage for fixed rational e, with coefficient bit lengths O(log N);
there is no need to materialize the 2N cylinders to certify their total area.

## 5. Effective count schedule with cubic coefficient $1/2$

Set $N=\lceil2/e^2\rceil$. Then $d\le e^2$, and (5) implies
$$
 \delta\le\frac12ed+\frac{21}{10}e^2d.                      \tag{22}
$$
For completeness, the numerator of $\delta/(ed)$ satisfies
$$
 M_*(1+e/2+ed/4)+2e
 \le1+\frac52e+\frac{11}{10}e^2.
$$
One may use $M_*\le1+(81/80)e^2$ and $d\le e^2$ to check this.
Moreover,
$$
 (1-e)(1+\tfrac{21}{5}e)
 -(1+\tfrac52e+\tfrac{11}{10}e^2)
 =\frac7{10}e-\frac{53}{10}e^2\ge0
$$
for $e\le1/10$, proving (22).
The superficially slightly sharper bound
$\delta\le ed/2+2e^2d$ is false at $e=1/10,d=e^2$, so is not used.

Together, (17), (18), and (22) give the explicit schedule bound
$$
 \boxed{\displaystyle
 R_{\rm sec}(e,\lceil2/e^2\rceil)
 \le\frac12-\frac{e^2}{60}+\frac12e^3+\frac92e^4,
 \qquad 0<e\le1/10.}                                      \tag{23}
$$
Here is a convenient rational bookkeeping check for its last coefficient:
$$
 \left(M_*+\frac38M_*^2\right)e^2d\le\frac75e^4,\quad
 M_*\delta\le\frac12e^3+\frac{109}{50}e^4,
$$
$$
 \delta^2/2\le\frac3{1000}e^4,\qquad
 M_*^2e^2d^2/16\le\frac1{1000}e^4,\qquad 4e^6\le e^4/25.
$$
The sum of the resulting quartic coefficients is
$$
 \frac{929}{1260}+\frac75+\frac{109}{50}
        +\frac1{250}+\frac1{25}<\frac92.
$$
For the bound on $M_*\delta$, use
$\delta\le(71/100)e^3$ and
$(M_*-1)\delta\le(81/80)e^2(71/100)e^3<(2/25)e^4$.

In particular,
$$
 \boxed{\displaystyle
 0<e\le1/50
 \quad\Longrightarrow\quad
 R_{\rm sec}\le\frac12-\frac{73}{15000}e^2<\frac12,
 \qquad 2N=2\lceil2/e^2\rceil.}                             \tag{24}
$$
In physical angular notation, (23) reads
$$
 R_{\rm sec}\le\frac12-\frac{\tau^2}{240}
                       +\frac{\tau^3}{16}
                       +\frac9{32}\tau^4,\qquad
 N=\lceil8/\tau^2\rceil.
$$

The cubic coefficient also describes the actual asymptotic area of this
specified construction:
$$
 R_{\rm sec}(e,\lceil2/e^2\rceil)
 =\frac12-\frac{e^2}{60}+\frac12e^3+O(e^4).                  \tag{25}
$$
Indeed $d=e^2+O(e^4)$ and (5) gives
$\delta=ed/2+(7/4)e^2d+O(e^3d+e^2d^2)=e^3/2+O(e^4)$.
The unpadded maximum-cap secant sum differs from $J(e)$ by $O(e^2d)$.
The coefficient of its linear padding term is
$\frac12\sum_i d_i\widehat M_i g_i^{\rm sec}=1+O(e^2)$;
the remaining padding term is $O(\delta^2)$.
This proves (25). It asserts no optimality of $1/2$ over other compatible
sector constructions.

## 6. Explicit $20000$-triangle point and the angular candidate

At $e=1/10,\ N=10000,\ d=1/5000$, formula (5) gives
$$
 M_*=1.01005625,\qquad
 \delta=0.00001400626791979166\ldots<0.00001401.
$$
The displayed decimal is only a convenience: the exact value is the
rational expression (5), which determines the construction.

Equation (18) supplies a completely analytic certificate
$$
 \boxed{R_{\rm sec}(1/10,10000)<0.499929.}                    \tag{26}
$$
For example, (17) is less than $0.499911064$, the first finite term in
(18) is less than $0.0000028$, the secant-weight term is less than
$0.000000000026$, and
$M_*\delta+\delta^2/2<0.000014164209$. Their sum is below $0.499929$.
This is an upper bound, not an evaluation of the exact finite sum (4).
Its exact finite maximum tangent is $\sqrt3(1/10)(9999/10000)$.

The previously conditional source-form candidate has
$$
 \eta=1/1000,\quad\tau=1/5,\quad N=10000,\qquad
 S(q)=1/2+\tau^2\{h(q)/8+\eta\}.
$$
Twice its physical radial cap is
$$
 R_L(q)=1+e^2\{h(q)+1/125\},\qquad e=1/10.
$$
Its excess over $C_e(q)$ is independent of $q$:
$$
 R_L(q)-C_e(q)=\frac{19}{800000}=0.00002375>\delta.           \tag{27}
$$
Therefore (16) proves that this finite compatible-cap candidate covers
the entire closed $K$. Its cell-maximum triangular version also covers,
with the same secant axes and exactly the same count.

The earlier [comparison note](research/published-radial-angular-comparison.md)
proved an area bound $R_L^{\rm finite}<0.499937$ for the curved-cap
version without assuming coverage. The missing coverage statement is now
supplied by (27). Passing to cell maxima adds less than $0.0000021$:
the cap $R_L$ has total variation $2e^2$, maximum $1.01008$, so the
increase is at most $1.01008e^2d=0.00000202016$.
Consequently its triangular enlargement has area below $0.499940$.
Both are now rigorous covering competitors to the previous radial
frozen-triangle value $>0.499947504745824$.

This does not show that those candidates lay in the angular paper's
original proved parameter range. Their coverage at $\tau=1/5$ uses the
new certificate (11)--(16). For published-range comparisons the original
source hypotheses must still be imposed. The new cap (2) is smaller than
this candidate's cell-maximum cap on every interval, so, with their
identical axes, the new triangular construction is strictly cheaper than
that particular triangular competitor.

## 7. Scope and independent certificate

The construction uses the published secant axes, shared-side first crossing,
and direct triangular intercept sectors. The quantitative novelty here is
the explicit quartic continuous certificate combined with (13)--(15),
which yields finite padding $ed/2+O(e^2d+e^2d^2)$, the count bound (23),
and a much larger certified parameter range for the source-form candidate.

It does not assert optimality among all covers, all cap profiles, all
partitions, or all compatible sectors. In particular, the cubic lower
bound for full constant-cap frozen-sweep enclosure is a different
constraint and is not contradicted.

The proof is algebraic and uniform; no coverage sampling, numerical
optimization, or large computation is used. The exact finite area in (4)
can be independently certified with rational bounds on square roots.



The independent verifier is [verification/secant_verify.py](verification/secant_verify.py).
It reconstructs (8), the physical-sign polynomial identity (11), and the
perturbation before bounding it; it does not import the generator into its
acceptance proof. It then bounds the exact sum (4) using rational Taylor
bounds and exact polynomial power sums. The constructor is loaded only for
separate physical-metric, projection, vertex, and area regression checks.
See [the report](verification/secant-report.md) for outward intervals and
[the saved run](verification/secant-last-run.txt) for reproduction output.
No point-cloud check substitutes for Sections 2–3, and no Lean build is claimed.

## 8. Published comparison at the finite benchmark

Set e=1/10 and N=10000. Compare at most 20000 cylinders and an actual maximum
axis tangent at most sqrt(3)*e*(1-1/N), measured from the corresponding
horizontal equality edge. The cited generic and radial estimates below allow
even the slightly larger budget sqrt(3)/10, so they apply here as well.

| Published construction and resource convention | Actual-area, count, or angle obstruction |
|---|---|
| Radial L/C/F/S, all explicit source sufficient ranges; arbitrary partitions/tags, projected bases or larger enclosures | R>=1/2-1/23328000>0.49999995, allowing retuned source tilt |
| Quantitative angular maximum caps, including optimizing the retained-mesh budget; cubic-buffer family | R>=1/2-1/93312000 |
| General compatible angular family on its explicit proof witness | R>=1/2-1/5529600000; its full list also has at least 36864000 cylinders |
| Direct endpoint and squared constructions | Respectively at least 392000002 and 800000000 cylinders |
| Alternative local Cartesian certificate | Any resulting complete cover has R>0.499999999996 |
| Rational/singular full retained-grid recipe | R>=637/1250>1/2 at this count and angle budget |
| Rational product/log recipe with published saving-error allocation | Over 20 million selected main cylinders in one family, including after finite-subcover selection |
| Nilpotent construction with prescribed apex lists | More than 34133 cylinders from the apex lists alone |
| Shortened beams with the prescribed strip | A strip axis deviates by more than arctan(1/3), outside the budget even after tetrahedron symmetries |

All numerical area floors exceed the new certified upper bound 0.499922.
The geometric lower bounds, exact source witnesses and count conventions are
proved in [published-proof-ranges.md](research/published-proof-ranges.md),
[the radial/angular comparison](research/published-radial-angular-comparison.md),
and [the generic comparison](verification/published-generic-comparison.md).
The slope-field note adds fixed-parameter asymptotic comparisons; those are
identified as guarantee comparisons, not substituted for finite actual costs.

The benchmark concerns the audited published recipes on the explicit
sufficient ranges supplied by their proofs, as selected by the user. It does
not claim that every possible witness of an existential smallness theorem
obeys the published numerical witness, or that larger valid ranges are
impossible. Fixed-positive-margin families also have the same-count,
exact-angle asymptotic comparison in the radial/angular note. The improvement
is not domination over every possible new instance of a generic method:
redesigned cell deletion, error allocations or newly proved cap admissibility
would require a separate comparison. Section 6 already gives one such new
admissibility result. No global optimality of tetrahedron covers is asserted.

## 9. Inequality dependencies and reproduction

| Estimate | Domain | Role and dependencies |
|---|---|---|
| First crossing and nonnegative selected radii | Any positive partition, closed K | Shared endpoint values D(q), with zero radii handled before division |
| Continuous square (11) | p,q in [-1,1], 0<e<1 | Exact polynomial identity; all remaining terms nonnegative |
| Discrete weights and loss (10), (13)–(15) | Same domain | Weight>=1-e; secant interpolation and cap bound M_* |
| Padding (1), (16) | 0<e<1 | Contradiction to simultaneous strict cap failure |
| Exact projected area (4) | Same construction | Normal axis component one; A_min=sqrt(2) |
| Uniform error (18)–(21) | 0<e<=1/10, any positive partition | Total variation 2e^2, derivative bound 3e^2, secant correction |
| Count condition (21a) | e<=1/10, N>=ceil(480/e) | Continuum Taylor bound plus uniform finite error |
| Source count schedule (23)–(24) | e<=1/10; saving e<=1/50 | d<=e^2, explicit padding bound and rational remainder sum |
| Exact numerical interval | e=1/10, N=10000 | Rational inverse-square-root bounds and exact power sums |

The projection normalization can also be recovered directly. The four face
area vectors are (0,±H,-1),(±H,0,1). For a unit axis v, Cauchy's polytope
projection formula gives

$$
A(v)=\max(H|v_x|,|v_z|)+\max(H|v_y|,|v_z|)\ge H.
$$

To check the inequality, put U=max(|v_x|,|v_z|/H),
V=max(|v_y|,|v_z|/H). Then U^2>=v_x^2, V^2>=v_y^2 and
2UV>=2v_z^2/H^2=v_z^2, so (U+V)^2>=1. Equality holds at the x-axis.
Thus A_min=H, with no body rescaling hidden in (4).

From the worktree root, run:

```sh
python3 topics/cylinder-covering/verification/verify.py
python3 topics/cylinder-covering/verification/secant_verify.py
python3 topics/cylinder-covering/secant_construction.py --epsilon 1/10 --n 10000 --index 0
```

Only standard-library Python is required. The generator returns exact rational
coordinates (x,y,z/sqrt(2)) with metric diag(1,1,2), the axis, projected triangle,
and its exact area expression. The source revision and all 91 snapshot hashes
are recorded in [sources/manifest.json](sources/manifest.json).
