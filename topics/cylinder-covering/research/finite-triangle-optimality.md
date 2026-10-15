# Exact local triangle optimum and a sharp finite-count cubic term

This note proves optimality only in the explicitly declared enclosure class.
Each midpoint cell must enclose the full constant-maximum-cap box sweep, and
the allowed triangle has the form $u\le U,\ |W|\le\ell(u+V)$.
It is not an optimality statement for arbitrary cylinders covering the body,
actual nonconvex sweep bases, the original variable-cap cell, or triangles
with arbitrary orientation. Novelty classification requires the separate
source audit; the arguments here establish the mathematical claims.

## 1. The local problem

Fix $a,k,M>0$ with $ka/M\le1/2$. Let

$$
 S_{a,k,M}=\{(u,W):u=\rho-sb,\ W=b\rho-sb^2/2,
       |b|\le a,\ |s|\le k,\ 0\le\rho\le M\}.              \tag{1}
$$

For $\ell>0$, consider the closed nondegenerate triangle

$$
 T(U,\ell,V)=\{(u,W):u\le U,\ |W|\le\ell(u+V)\}.           \tag{2}
$$

It is symmetric about the $u$-axis, with its apex to the left of its
vertical opposite side. Its vertices are $(-V,0)$ and
$(U,\pm\ell(U+V))$, and its coordinate area is
$\ell(U+V)^2$. The requirement $U+V>0$ is part of nondegeneracy.

**Local theorem.** Among the triangles (2) that contain (1), the unique
minimum-area choice is

$$
 U_0=M+ka,\qquad \ell_0=a-\frac{ka^2}{M},\qquad
 V_0=ka+\frac{ka^2}{2\ell_0}.                                \tag{3}
$$

Writing $z=ka/M$, its exact minimum area is

$$
\begin{aligned}
 A_{\min}
 &=aM^2\frac{(1+3z/2-2z^2)^2}{1-z}\\
 &=aM^2\left[1+4z+
                \frac{z^2(3/2-2z)^2}{1-z}\right]
 \ge aM^2+4ka^2M.                                           \tag{4}
\end{aligned}
$$

### Necessary supports and the global minimum over all positive slopes

The maximum $u$ in (1) is $M+ka$, so every admissible triangle has
$U\ge U_0$. The support inequality $W-\ell u\le\ell V$
at $\rho=0,b=-a,s=-k$ gives

$$
 \ell V\ge k\ell a+ka^2/2=:h_0(\ell).                       \tag{5}
$$

At $\rho=M,b=a$, choosing the better sign of $s$ gives the
additional necessary support

$$
 \ell V\ge(a-\ell)M+ka|\ell-a/2|=:h_1(\ell).                \tag{6}
$$

In particular $V>0$, so area is strictly increasing in $U\ge U_0$.
For fixed $\ell$, it is also strictly increasing in $V$ above
the positive bound (5). Thus every feasible area is at least the one
obtained by taking $U=U_0$ and
$\ell V=\max(h_0,h_1)$. These are necessary bounds only; sufficiency
will be verified at the minimizing parameters, so no unproved support
description is needed away from the minimum.

Normalize $t=\ell/a$. For $0<z\le1/2$, the resulting necessary
area, divided by $aM^2$, is

$$
 F_z(t)=
 \begin{cases}
 (1+z/2)^2/t,&0<t\le1/2,\\
 (1-z/2+2zt)^2/t,&1/2\le t\le1-z,\\
 ((1+2z)t+z/2)^2/t,&t\ge1-z.
 \end{cases}                                                \tag{7}
$$

To check the branches, when $t\le1/2$,
$h_1-h_0=aM[1-t(1+2z)]\ge0$. When $t\ge1/2$, their
difference is $aM(1-t-z)$, which changes sign at $t=1-z$.

The first branch is strictly decreasing. On the middle branch,

$$
 F_z'(t)=4z^2-\frac{(1-z/2)^2}{t^2}<0.
$$

Indeed $t\le1-z$ and
$1-z/2-2z(1-z)=(4z^2-5z+2)/2>0$; the last quadratic has
negative discriminant and positive leading coefficient. On the final
branch,

$$
 F_z'(t)=(1+2z)^2-\frac{z^2}{4t^2}>0,
$$

because $t\ge1-z\ge1/2$, so $z/(2t)\le z<1+2z$.
The formulas agree at both junctions. Therefore (7) has a unique global
minimum at $t=1-z$, including the boundary case $z=1/2$.
The corresponding necessary values are exactly (3), and (7) gives (4).

### Feasibility at the minimum

The support functionals are affine in $\rho$, so it suffices to
check $\rho=0,M$. At $\rho=0$,
$u\ge-ka$ and $|W|\le ka^2/2$, giving
$W-\ell_0u\le k\ell_0a+ka^2/2=\ell_0V_0$.

At $\rho=M$, the exact relation is
$W=b(M+u)/2$, with $M-ka\le u\le M+ka$. Since
$\ell_0\ge a/2$ and $M+u>0$,

$$
 W-\ell_0u\le aM/2+(a/2-\ell_0)(M-ka)
              =\ell_0V_0,
$$

where $(a-\ell_0)M=ka^2$ proves the equality. The symmetry
$(b,s,W)\mapsto(-b,-s,-W)$ gives the other sloping support.
The bound $u\le U_0$ always holds. Thus the triangle (3) really
contains (1), completing the optimality and uniqueness proof.

## 2. The finite-cover enclosure class

Fix the canonical quartic cap and projection weight

$$
 C_e(q)=1+e^2H(q)+\frac9{16}e^4,\qquad
 g_e(q)=(1+e^2D_0(q))^{-1/2},\qquad 0<e\le1/10.
$$

Choose any partition of $[-1,1]$ into $N$ positive-width intervals
$I_j$, with widths $d_j$ and midpoints $c_j$. Put
$M_j=\max_{I_j}C_e$. Freeze each axis at the midpoint and require its
intercept triangle to enclose the entire box sweep (1), with

$$
 a_j=d_j/2,\qquad k=2e,\qquad M=M_j.
$$

These are enlarged constant-cap cell sweeps. They contain the original
variable-cap sweep, so their enclosing cylinders cover the body by the
separate quartic overlap proof. The other family is obtained by the
orthogonal symmetry, giving exactly $2N$ labeled cylinders.

Since $M_j\ge1$, $d_j\le2$, and $e\le1/10$,
$ka_j/M_j=ed_j/M_j\le1/5<1/2$, so the local theorem always applies.
For a fixed partition, choosing (3) in every cell is therefore exactly
area-optimal within this triangle class. Projection multiplies each
cell's coordinate area by a fixed positive factor and does not change
its local minimizer.

Let $\mathcal I_N(e)$ be the infimum of the normalized total cost over
all these $N$-cell midpoint partitions and all their feasible triangles
of the form (2). Put

$$
 J(e)=\frac14\int_{-1}^1 C_e(q)^2g_e(q)\,dq,\qquad
 M_*=1+e^2+9e^4/16,\qquad g_*=(1+3e^2)^{-1/2}.
$$

**Finite-count lower bound.**

$$
 \boxed{\mathcal I_N(e)\ge J(e)+\frac{4e}{N}
       \left[g_*-\frac3{16}M_*^2e\right].}                  \tag{8}
$$

For each cell, (4) implies

$$
 A_j\ge\frac{d_jM_j^2}{2}+2eM_jd_j^2.
$$

The two-family normalized cost is $\frac12\sum_j A_jg_e(c_j)$.
Hence it is at least

$$
 \frac14\sum_j d_jM_j^2g_e(c_j)
                        +e g_*\sum_jd_j^2.                 \tag{9}
$$

In its first term, $M_j^2\ge C_e(q)^2$. The only possibly negative
error against $J(e)$ comes from freezing the weight. Since
$|g_e'|\le3e^2$ and
$\int_{I_j}|q-c_j|\,dq=d_j^2/4$, that error is at most

$$
 \frac3{16}M_*^2e^2\sum_jd_j^2.
$$

Thus (9) is bounded below by
$J(e)+e[g_*-(3/16)M_*^2e]\sum_jd_j^2$. The coefficient is positive
throughout the stated range. Finally $\sum_jd_j=2$ gives
$\sum_jd_j^2\ge4/N$, proving (8).

The uniform partition and the optimal local triangles are members of this
class. The existing uniform error estimate therefore supplies

$$
 \mathcal I_N(e)\le J(e)+\frac{4e}{N}+\frac{8e^2}{N}
          +\frac{81e^3}{20N}+\frac{8e^2}{N^2}.               \tag{10}
$$

Combining (8),(10), using $g_*\ge1-3e^2/2$, proves uniformly

$$
 \mathcal I_N(e)=J(e)+\frac{4e}{N}
                      +O\left(\frac{e^2}{N}+\frac{e^2}{N^2}\right).
                                                                    \tag{11}
$$

This is a finite resource lower bound over all midpoint partitions in the
declared class. It is stronger than optimizing the triangle on one already
chosen partition. It does not assert that the uniform partition minimizes
the entire finite cost exactly.

## 3. The cubic coefficient is sharp on the published count schedule

On $N(e)=\lceil2/e^2\rceil$, the continuum expansion and (11) give

$$
 \boxed{\mathcal I_{N(e)}(e)=\frac12-\frac{e^2}{60}
                                  +2e^3+O(e^4).}           \tag{12}
$$

Equivalently, with physical slope convention $\tau=2e$, the sharp
cubic coefficient is $1/4$ in
$1/2-\tau^2/240+\tau^3/4+O(\tau^4)$. No choice of nonuniform
midpoint partition or feasible local triangle (2) can lower that coefficient
while keeping this cap and the same $2\lceil8/\tau^2\rceil$ count.

An explicit two-sided bound, avoiding an unspecified remainder, is

$$
 \frac12-\frac{e^2}{60}+2e^3-\frac45e^4
 \le\mathcal I_{N(e)}(e)
 \le\frac12-\frac{e^2}{60}+2e^3+\frac52e^4
 \qquad(0<e\le1/10).                                       \tag{13}
$$

For the lower bound, first note that $J(e)\ge1/2-e^2/60$ on this
range. Indeed, keep $1+2e^2H+(9/8)e^4$ from $C_e^2$, multiply
by the positive lower weight $1-e^2D_0/2$, and integrate. This gives

$$
 J(e)\ge\frac12-\frac{e^2}{60}
                  +\frac{1507}{5040}e^4-\frac{51}{160}e^6
 \ge\frac12-\frac{e^2}{60}.                                 \tag{14}
$$

Next $M_*<1.011$ implies $(3/16)M_*^2<1/5$, so the bracket
in (8) is at least $1-e/5-3e^2/2>0$. The ceiling satisfies

$$
 \frac{4e}{N(e)}\ge\frac{4e^3}{2+e^2}\ge2e^3-e^5.
$$

Consequently its product with that bracket is at least
$2e^3-(2/5)e^4-4e^5\ge2e^3-(4/5)e^4$, proving the left side
of (13). The right side is the sharper uniform-grid estimate already
proved in `THEOREM.md`, Sections 4–5, using the same local minimizer.

These exact lower bounds do not imply a universal lower bound for all
finite covers. In particular, the full constant-maximum-cap cell condition
is stronger than enclosing the actual variable-cap sweep, and the declared
triangle geometry excludes other enclosures. The sharp coefficient in
(12) is a precise obstruction inside this class, not an obstruction to
improving the overall cylinder-covering construction.

All arguments in this note are analytic. No numerical optimization,
sampling, or further computational experiment was used.
