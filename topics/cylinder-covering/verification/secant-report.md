# Independent secant-cover verification

The compatible-secant quartic construction passes exact algebraic verification,
universal coverage and error estimates, and independent generator checks. At
$e=1/10,N=10000$, its 20,000 triangular cylinders have normalized total area

$$
\boxed{0.499921585997001674\le R_{\rm secant}
\le0.499921585997001774<1/2.}
$$

This is smaller than the earlier radial-triangle certificate. The source's
explicit fixed-positive-margin range is also now compared using its pinned
formal constants; the absence of those constants in the manuscript summary is
no longer a gap in this comparison.

Run from the repository root:

```sh
python3 topics/cylinder-covering/verification/secant_verify.py
```

The focused run passed in approximately 0.15 seconds. The checker uses exact
rational arithmetic, polynomial identities, signed Taylor remainders, and
integer power sums. It reuses only the previously checked polynomial and
arithmetic utilities from `verify.py`. Coverage equations, padding, total area,
and regression expectations are reconstructed independently of
`secant_construction.py`, which is imported only for output checks. There are
no sampled coverage tests or floating-point acceptance decisions. This is not
a Lean kernel verification of the new theorem.

## 1. Closed coverage from compatible secant boundaries

Use the physical tetrahedron

$$
K=\{(x,y,\sqrt2s):0\le s\le1,\ |x|\le1-s,\ |y|\le s\},
\qquad A_{\min}=\sqrt2.
$$

For each interval $I=[l,r]$ of width $d=2/N$, write

$$
a_I=(1+lr)/2,\qquad b_I=(l+r)/2,\qquad h_I(q)=a_I-qb_I.
$$

The two families have axes
$(1,ea_I,\sqrt2eb_I)$ and $(-ea_I,1,\sqrt2eb_I)$. With

$$
G(q)=(1+q^2)/2,\quad D_-(q)=(1-q^2)/2,
\quad H(q)=q^2G(q),\quad C(q)=1+e^2H(q)+9e^4/16,
$$

the checker verifies the exact secant identities

$$
(r-l)h_I(q)=(r-q)D_-(l)+(q-l)D_-(r),
\qquad h_I(q)-D_-(q)=-\frac{(q-l)(r-q)}2.
\tag{1}
$$

They imply that the piecewise affine boundary $h$ is continuous,
nonnegative, and zero at (-1,1). They also give, for every $q\in I$,

$$
0\le a_I\le1,\quad |b_I|\le1,\quad
|a_I-G(q)|\le d/2,\quad |b_I-q|\le d/2,\quad
|h_I(q)-D_-(q)|\le d^2/8.
\tag{2}
$$

For the bound on $a_I-G(q)$, use the checked identity
$q^2-lr=q(q-r)+r(q-l)$, together with $|q|,|r|\le1$.

Given any point of $K$, the continuous piecewise affine functions

$$
F(q)=sq+exh(q),\qquad P(p)=(1-s)p-eyh(p)
$$

have endpoint values ((-s,s)) and ((-(1-s),1-s)). A first crossing of
the respective target values $y,x$ gives a root on a cell where the
one-sided slope is nonnegative. If a target is attained on a constant cell,
choose that cell. If a target is an endpoint value and the initial slope
points away from the target, the endpoint inequality ensures a later return
crossing. Thus closed endpoints and zero slopes are included.

On the selected cells, put $S=s-exb_q\ge0$, $T=1-s+eyb_p\ge0$, and
rescale $X=2x,Y=2y,\rho=2S,\sigma=2T$. The underlying equations are

$$
Y=\rho q+eXa_q,\quad X=\sigma p-eYa_p,\quad
\rho+\sigma=2+e(Yb_p-Xb_q).
\tag{3}
$$

Independent elimination with $D=1+e^2a_pa_q$ gives

$$
DX=\sigma p-e\rho qa_p,\qquad
DY=\rho q+e\sigma pa_q,
$$

$$
W_q\rho+W_p\sigma=2D,
$$

where

$$
W_q=1-eqb_p+e^2a_ph_q,\qquad
W_p=1+epb_q+e^2a_qh_p.
\tag{4}
$$

By (1)--(2), $W_p,W_q\ge1-e>0$. This argument divides by neither $S$
nor $T$; apex and zero-radius cases are covered.

## 2. Exact padding from the quartic certificate

For the continuous coefficients $a_q=G(q),b_q=q$, let the corresponding
weights be $W_q^0,W_p^0$, and $D^0=1+e^2G(p)G(q)$. The checker
reconstructs the signed version of the quartic certificate. With
$\Delta=p^2-q^2$, $Z=1+p^2+q^2$, it is

$$
\begin{aligned}
W_q^0C(q)+W_p^0C(p)-2D^0
={}&\frac{e^2}{2}(\Delta+epqZ/2)^2\\
&+e^4\left[G(p)G(q)(p^2D_-(p)+q^2D_-(q))
                  +\frac{9-p^2q^2Z^2}{8}\right]\\
&+\frac9{16}e^6\left[G(p)D_-(q)+G(q)D_-(p)\right]\ge0.
\end{aligned}
\tag{5}
$$

Nonnegativity of the only less immediate factor is checked by its polynomial
decomposition

$$
9-p^2q^2Z^2
=9\{(1-p^2)+p^2(1-q^2)\}
+p^2q^2\{(1-p^2)+(1-q^2)\}(3+Z).
$$

Let $M_*=1+e^2+9e^4/16$. Subtracting (5)'s continuous residual from the
discrete residual in (4) and grouping the exact terms gives a loss bounded by

$$
L(e,d)=M_*ed+M_*e^2(d/2+d^2/4)+2e^2d.
\tag{6}
$$

Here the linear coefficient errors contribute $M_*ed$; the two products
$a_ph_q$, $a_qh_p$ contribute $M_*e^2(d/2+d^2/4)$; and the
denominator change contributes $2e^2d$. The checker verifies this
decomposition before applying the universal bounds (2).

The independently reconstructed padding is therefore

$$
\delta(e,d)=\frac{L(e,d)}{2(1-e)}
=\frac{d[M_*(e+e^2/2)+2e^2+M_*e^2d/4]}{2(1-e)}.
\tag{7}
$$

Adding $\delta$ to each cap compensates (6), since
$W_p+W_q\ge2(1-e)$. Simultaneous strict failures
$\rho>C(q)+\delta$, $\sigma>C(p)+\delta$ would contradict
(4)--(7). Hence at least one selected radius is within its cap.

On interval $I_j$, replace $C(q)$ by
$M_j=\max_{I_j}C$, and set $T_j=(M_j+\delta)/2$. The corresponding
physical intercept triangle has vertices

$$
(0,0,0),\quad(0,l_jT_j,\sqrt2T_j),\quad
(0,r_jT_j,\sqrt2T_j),
$$

with the upper family obtained by the stated symmetry. Since the selected
intercept is $(0,qS,\sqrt2S)$ with $0\le S\le T_j$, it belongs to this
closed triangle. This completes coverage of every point of the closed body,
for every $N\ge1$ and $0<e\le1/10$, using exactly $2N$ cylinders.

## 3. Exact physical cost, angle, and generator regression

Let $c_j$ be the midpoint and $d=2/N$. Then

$$
a_j=G(c_j)-d^2/8,\quad b_j=c_j,\quad
D_j=a_j^2+2c_j^2.
$$

The exact normalized two-family cost is

$$
R_{e,N}=\frac d4\sum_{j=1}^N
\frac{(M_j+\delta)^2}{\sqrt{1+e^2D_j}}.
\tag{8}
$$

The maximum of $D_j$ occurs at an outer midpoint. There
$a_j=|c_j|=1-1/N$, so the exact finite maximum tangent is

$$
\sqrt3e(1-1/N).
\tag{9}
$$

This vanishes for $N=1$, as the two directions are then exactly the equality
edges. For the main instance it is smaller than the allowance
$\sqrt3/10$ used in the baseline comparisons.

In scaled coordinates $(x,y,z/\sqrt2)$, the metric is
$\operatorname{diag}(1,1,2)$. The checker independently verifies 36
representative generator outputs: both families, $e=1/100,1/10$,
$N=1,2,3,10000$, central and outer intervals. It checks the exact axes,
intercept vertices, padding, cutoffs, parallel projection displacements,
perpendicularity, positive Gram determinants, and the complete base areas.
The squared area divided by $A_{\min}^2$ is the Gram determinant divided
by eight. The printed generator formula agrees exactly with that computation.

## 4. Uniform finite error and the schedule

Put

$$
J(e)=\frac14\int_{-1}^1\frac{C(q)^2}{\sqrt{1+e^2D_0(q)}}\,dq,
\qquad D_0(q)=G(q)^2+2q^2.
$$

The previous independent cap calculation established

$$
\frac12-\frac{e^2}{60}-\frac{83}{315}e^4
\le J(e)\le
\frac12-\frac{e^2}{60}+\frac{929}{1260}e^4+4e^6.
\tag{10}
$$

An independent upper error estimate for (8) is

$$
R_{e,N}-J(e)\le
\left(M_*+\frac38M_*^2\right)e^2d
+M_*\delta+\frac{\delta^2}{2}
+\frac{M_*^2e^2d^2}{16}.
\tag{11}
$$

The first term bounds the interval-maximum and midpoint-freezing errors.
Apply the secant weight correction to the unpadded cap first, and then bound
the padding contribution using the secant weight's upper bound of one. The
next two terms in (11) bound this cap-square enlargement. For the final term,

$$
0\le D_0(c_j)-D_j=G(c_j)d^2/4-d^4/64\le d^2/4,
$$

and the derivative of $(1+e^2D)^{-1/2}$ has absolute value at most $e^2/2$.

Using $M_*<1011/1000$, $M_*^2<1023/1000$,
$M_*+3M_*^2/8<7/5$, and $\delta\le3ed/4$, the entire upper error
in (11) is at most

$$
\left(\frac{3033}{4000}+\frac9{160}+\frac7{50}
+\frac{1023}{80000}\right)ed
=\frac{77383}{80000}ed<ed.
$$

The lower error from freezing is smaller than $ed$. Hence, for every
$N\ge1$,

$$
\boxed{|R_{e,N}-J(e)|\le ed=2e/N.}
\tag{11a}
$$

This bound gives a second explicit count guarantee, without imposing the
$e^{-2}$ schedule: the checker verifies
$(929/1260)/100+4/10000<1/120$, so (10) yields
$J(e)\le1/2-e^2/120$. Therefore

$$
\boxed{N\ge\lceil480/e\rceil\quad\Longrightarrow\quad
R_{e,N}\le\frac12-\frac{e^2}{240}<\frac12,
\qquad0<e\le1/10.}
\tag{11b}
$$

Conversely, the secant projection weight is at least the midpoint smooth
weight. The added cap contributes at least
$\delta(1+3e^2)^{-1/2}$, while freezing loses at most
$3M_*^2e^2d/8$. Thus

$$
R_{e,N}-J(e)\ge
\delta(1+3e^2)^{-1/2}-3M_*^2e^2d/8.
\tag{12}
$$

The checker verifies the exact expansion of (7) about $ed/2$ and the
rational endpoint bounds giving

$$
ed/2\le\delta\le ed/2+(5/2)e^2d\le(3/4)ed
\quad(0<e\le1/10,\ 0<d\le2).
$$

Substitution in (11)--(12) yields the convenient uniform estimate

$$
\boxed{|R_{e,N}-J(e)-ed/2|\le5e^2d.}
\tag{13}
$$

In particular, the leading finite correction is $e/N$, with relative error
at most (10e), uniformly for all $N\ge1$. For
$N=\lceil2/e^2\rceil$, (10)--(13) give

$$
R_{e,N}=\frac12-\frac{e^2}{60}+\frac12e^3+O(e^4),
$$

and the explicit upper bound

$$
R_{e,N}\le\frac12-\frac{e^2}{60}+\frac12e^3+6e^4.
$$

Consequently $R_{e,N}\le1/2-e^2/2400<1/2$ throughout
$0<e\le1/40$. Independently checking the sharper construction bookkeeping
also gives

$$
R_{e,N}\le\frac12-\frac{e^2}{60}+\frac12e^3+\frac92e^4
\qquad(N\ge\lceil2/e^2\rceil,\ 0<e\le1/10).
\tag{13a}
$$

For this check, $d\le e^2$ improves the padding estimate to
$\delta\le ed/2+(21/10)e^2d\le(71/100)e^3$. Its proof follows from
$M_*\le1+(81/80)e^2$ and the exact identity

$$
(1-e)(1+21e/5)-(1+5e/2+11e^2/10)
=7e/10-53e^2/10\ge0.
$$

The checked quartic upper contributions, in order from (10)--(11), are

$$
\frac{929}{1260}+\frac75+\frac{109}{50}
+\frac3{1000}+\frac1{1000}+\frac1{25}<\frac92.
$$

In particular (13a) gives the stronger margin $73e^2/15000$ throughout
$e\le1/50$, as asserted in the construction note. The coefficient $1/2$
is the asymptotic coefficient of this secant recipe; no global optimality
claim is made.

## 5. Certified sums without enumerating the cylinders

On positive midpoint cells, $M_j=C(c_j+d/2)$ is a rational polynomial in
the index. The padding is independent of the index, and $D_j$ is also a
polynomial. The degree-nine lower and degree-eight upper Taylor polynomials
of $(1+x)^{-1/2}$, multiplied by $(M_j+\delta)^2$, therefore enclose the
summands in (8). Taylor's integral remainder has the required sign for every
$x\ge0$. Exact binomial power sums aggregate the whole list; odd $N$
has one separately evaluated central interval.

The sums were independently cross-checked for $N=1,2,3,7$ using direct
integer-square-root enclosures. The displayed bounds are rounded outward from
exact rational results:

| $e$ | $N$ | Cylinders | Certified secant ratio interval |
|---|---:|---:|---|
| $1/10$ | 10,000 | 20,000 | [0.499921585997001674, 0.499921585997001774] |
| $1/100$ | 20,000 | 40,000 | [0.499998863418315727, 0.499998863418315728] |
| $1/1000$ | 2,000,000 | 4,000,000 | [0.499999983836322736, 0.499999983836322737] |

All three save area. The middle row is a real improvement over the earlier
radial-triangle recipe, whose corresponding exact area was above $1/2$.

The previously conditional angular continuous cap with $\tau=1/5$,
$\eta=1/1000$, and $N=10000$ also satisfies the new coverage certificate.
Indeed $\tau=2e$, and its twice-cutoff is
$1+e^2H(q)+(1/125)e^2$. The checker verifies

$$
\frac9{16}e^4+\delta(e,2/N)<\frac1{125}e^2
$$

at these parameters. Its coverage is supplied by this new proof, not by
extending an older sufficient threshold without justification.

## 6. The source's proved compatible-cap range

The pinned formal companion makes the sufficient range explicit in
[`GeneralCoverage.lean`](../sources/lean/OAI/Geometry/CylinderCovering/Angular/GeneralCoverage.lean):

$$
E\ge0,\quad0<\eta\le1/480,\quad0<\tau\le1/2,
\quad(10+4E)\tau\le\eta.
\tag{14}
$$

[`GeneralAssembly.lean`](../sources/lean/OAI/Geometry/CylinderCovering/Angular/GeneralAssembly.lean)
proves an error of at most $(6E+2)\tau^4$ from
$1/2+(2\eta-1/240)\tau^2$. Its additional condition
$E\tau^2\le1/16$ follows from (14), since
$E\tau^2\le\eta\tau/4\le1/3840$. The physical area equals this integral
cost by [`GeneralVolume.lean`](../sources/lean/OAI/Geometry/CylinderCovering/Angular/GeneralVolume.lean).

Because $6E+2\le2(10+4E)$, the positive margin term absorbs the error.
Also $\tau\le1/4800$. Therefore every instance in this proved range has

$$
R\ge\frac12-\frac1{5529600000}
>0.499999999819155092.
\tag{15}
$$

There is also an exact count obstruction. The coefficient hypotheses in
[`GeneralDefinitions.lean`](../sources/lean/OAI/Geometry/CylinderCovering/Angular/GeneralDefinitions.lean)
give $|\beta_j-q/2|\le E\tau^2$ at both endpoints of every interval,
so each width is at most $4E\tau^2$. A positive-width finite partition
requires $E>0$, and its full two-family count $2N$ obeys

$$
2N\ge\frac1{E\tau^2}\ge\frac{(10+4E)^2}{E\eta^2}
\ge\frac{160}{\eta^2}\ge36{,}864{,}000.
\tag{16}
$$

The final optimization is certified by
$(10+4E)^2-160E=(4E-10)^2\ge0$. Thus this published range cannot
compete at 20,000 cylinders, and its actual area floor also exceeds the new
secant result.

These comparisons use the source's proved sufficient ranges and full count
conventions. They do not claim that (14) is a necessary geometric condition
for any compatible-cap cover. The new certificate itself proves coverage of
some formerly unproved parameter choices outside (14). The beam, apex, grid,
and product/logarithmic obstructions in
[the generic comparison](published-generic-comparison.md) continue to apply
at the same allowance and count, since the secant ratio is even smaller.
