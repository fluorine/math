# Published slope fields: exact coefficient gaps and finite limitations

15 October 2026. Baseline scope follows the user's clarification: published
constructions on their proved parameter ranges and count conventions. This note
records exact analytical comparisons supplied by the independent source reader
and integrated by the primary. It does not replace the distinction between a
source upper-bound guarantee and the area of its actual finite realization.

Source: the pinned *Slope-field perturbations of the two-cylinder covering*,
`build/sections/rational.tex`, `dictionary.tex`, and `singular.tex`.
All ratios below use total physical base area divided by the body's minimum
projection area; similarities of the tetrahedron preserve that ratio.

## 1. Rational regularization: a strict quadratic gap

Fix the published regularization parameter d>0 and let

$$
\alpha=(1+2d)^{-1}\in(0,1),\qquad
f(s)=\frac56-\frac s3+\frac{s^2}{15}.
$$

On the original label triangle write r=t/2, 0<=t<=1, q=2Y/r, |q|<=1, and

$$
s=\frac{r}{r+d}=\frac{\alpha t}{1-\alpha+\alpha t}.
$$

The source field has

$$
a=-\frac{s[2+s(q^2-1)]}{16},\quad b=\frac{sq}{4},\quad
a^2+\frac{b^2}{2}
=\frac{s^2}{256}[(2-s+sq^2)^2+8q^2].
$$

The last expression increases with q^2 and with s on [0,1], so its
maximum is 3 alpha^2/64. Its physical maximum slope is therefore
sqrt(3)*alpha*epsilon/8. With the source's integrals I_d,J_d, integration
in q gives the exact identities

$$
\frac{256I_d}{\alpha^2}
=\int_0^1t\left(\frac{s}{\alpha}\right)^2f(s)\,dt,
\qquad
\frac{256J_d}{\alpha^2}=\frac{5-\alpha}{15}.
$$

Indeed these are ordinary polynomial integrals in q; the remaining rational
integral in t need not be evaluated using logarithms. Since

$$
(sf(s))'=\frac56-\frac{2s}{3}+\frac{s^2}{5}>0,
$$

and s<=alpha, we have (s/alpha)^2 f(s)<=(s/alpha)f(alpha). Also

$$
\frac{s}{\alpha}=\frac{t}{1-\alpha+\alpha t}
\le(1-\alpha)t+\alpha.
$$

After multiplication by the positive denominator, this last inequality is
exactly alpha(1-alpha)(1-t)^2>=0. Consequently the normalized quadratic
saving coefficient after matching epsilon=8e/alpha obeys

$$
\begin{split}
S_d:=\frac{256(I_d-J_d)}{\alpha^2}
&\le\frac{(2+\alpha)f(\alpha)}6-\frac{5-\alpha}{15}\\
&=\frac1{60}
-\frac{(1-\alpha)(2\alpha^2-4\alpha+13)}{180}
<\frac1{60}.
\end{split}
$$

This holds for every fixed d>0, including parameters that do not give a
positive saving. The positive padding q contributes +2q to the normalized
source prediction

$$
R_{\rm predicted}=\frac{4C_d(\epsilon,q)}h
=\frac12+4\epsilon^2(J_d-I_d)+2q+O_d(\epsilon^4).
$$

Here h=1/sqrt(2), and the published assumptions are q=O(epsilon^2) and
epsilon^3=o(q). The enlarged domain changes the maximum physical slope by
O_d(epsilon^3), so exact matching of its continuum maximum to sqrt(3)*e
changes epsilon=8e/alpha by O_d(e^3) and preserves the strict quadratic gap.
Using epsilon=8e at fixed d would be an incorrect physical normalization.

## 2. Singular power fields: a strict quadratic gap

With the source's fixed p>1, a=1/2 and coordinates (b,r), the physical axes are

$$
(1,cP,\sqrt2\,cQ),\qquad
P=\frac a2(r/a)^{p-1}[p+(2-p)(b/r)^2],\quad
Q=(r/a)^{p-2}b.
$$

On the original triangle 0<r<=a, |b|<=r, the maximum slope is sqrt(3)*c/2.
The source coefficient after matching c=2e to leading order is

$$
S_p=\frac{13-10p-2p^2}{60p}
=\frac1{60}-\frac{(p-1)(2p+13)}{60p}<\frac1{60}.
$$

The domain enlargement changes the continuum maximum only at higher order.
For every fixed published p and cutoff exponent, this gap survives exact
matching of continuum maximum physical tilt. Both this gap and the rational
gap vanish as their regularization parameters approach their limiting values.

## 3. A numerical guarantee comparison for the original singular padding

For the original choices q=c^(5/2), cutoff d=c^gamma and continuum slope
bounded by sqrt(3)/10, let

$$
F(c)=\frac{2J(c)}{\sqrt2}+8d^2.
$$

This is the source's integral-plus-tip cost before adding its positive finite
approximation tolerance. Throughout its published p interval,

$$
\int_{0<r\le1/2,\ |b|\le r}(P^2+2Q^2)
=\frac{2p^2+2p+13}{240p}\le\frac{17}{240}.
$$

The inverse-square-root bound 1/sqrt(1+x)>=1-x/2 on the original triangle
therefore gives loss at most 17c^2/240. Removing r<d loses label area at most
d^2 per family, whereas the two tips add 8d^2 to the normalized cost, leaving
a nonnegative surplus. The added rectangle |b|<=a, a<=r<=a+c^(5/2) has area
c^(5/2), and its projection weight is at least 1/sqrt(1.03)>19/20. Hence

$$
F(c)\ge\frac12-\frac{17}{240}c^2+\frac{19}{10}c^{5/2}
\ge\frac12-\frac{1419857}{126672012000000}>0.4999999887.
$$

The second inequality minimizes -Ac^2+Bc^(5/2), with A=17/240, B=19/10:
its minimum is -A(4A/(5B))^4/5. The rectangle proof needs d<=a and
a+c^(5/2)<=2. For 0<c<1 the second holds; if d>a, tip cost alone exceeds 2,
and if c>=1 the tip cost exceeds 8. These remaining cases do not improve
the source guarantee.

The source also permits flexible padding q=o(c^2), c^3=o(q). At a chosen
nonzero c those conditions give no uniform positive numerical lower bound
on q, so the displayed numerical comparison cannot be extended to all those
published specializations.

## 4. What follows, and what does not

For each fixed d>0 or fixed p>1 and the source's other fixed parameters,
the new construction on N=ceil(2/e^2) satisfies
R_N=1/2-e^2/60+o(e^2). It therefore eventually improves the respective
published limiting integral-plus-padding/tip guarantee at matched continuum
physical maximum tilt. This is a familywise asymptotic statement, with an
explicit positive quadratic coefficient gap.

It is not a uniform finite-budget comparison as d tends to zero or p tends
to one. It also is not a lower bound on the cost of the source's actual
finite cylinders. The finite approximation theorem supplies an upper-bound
tolerance, may use affine-approximation velocities, and does not equate
finite maximum-axis tilt with the continuum maximum. These distinctions
remain necessary even though the source does provide generic rate and count
machinery. No failure at 20000 cylinders follows from missing specialized
constants or from an unspecified source threshold.
