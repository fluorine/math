# Exact quartic radial padding

Status: proved by the elementary identities below; exact polynomial checks
passed. This note concerns the radial sweeps and their limiting area. A finite
count bound is a separate integration task. No claim to beat every source
construction follows from this note.

## 1. Source, normalization, and statement

Use the canonical regular tetrahedron

$$
 K_c=\{(x,y,ht): |x|\le 1+t,\ |y|\le1-t\},\qquad h=\sqrt2.
$$

Its edge length is four and its minimum projection area is $4h$. This is
exactly the normalization in the pinned radial manuscript's
[`tetrahedron.tex`](../sources/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/build/tetrahedron.tex),
equations `eq:tetrahedron`, `eq:upper-sweep`, and `eq:lower-sweep`. Put

$$
 G(r)=\frac{1+r^2}{2},\quad D(r)=\frac{1-r^2}{2},\quad
 H(r)=r^2G(r),\quad D_0(r)=G(r)^2+2r^2.
$$

For a continuous positive cap $R$ on $[-1,1]$, the upper and lower
sweeps are

$$
 U_R=\{(x,\rho q-e xG(q),h(1-\rho+e xq)):
 |x|\le2,\ |q|\le1,\ 0\le\rho\le R(q)\},
$$

$$
 L_R=\{(\sigma p+e yG(p),y,h(-1+\sigma+e yp)):
 |y|\le2,\ |p|\le1,\ 0\le\sigma\le R(p)\}.
$$

**Quartic cap theorem.** For every $0<e\le1$, the cap

$$
 \boxed{R_e(r)=1+e^2H(r)+\frac9{16}e^4}
$$

satisfies $K_c\subseteq U_{R_e}\cup L_{R_e}$, including all faces,
edges, and vertices. The coefficient $9/16$ is the least constant
$C$ for which caps $1+e^2H+Ce^4$ cover for every sufficiently small
positive $e$. This sharpness assertion is confined to that cap family.

The source's existing radial approximation theorem then supplies finite
triangular cylinder covers converging in cost to

$$
 2hQ(e),\qquad Q(e)=\int_{-1}^1
 \frac{R_e(r)^2}{2\sqrt{1+e^2D_0(r)}}\,dr.
$$

Thus cost divided by minimum projection area is $Q(e)/2$, not
$Q(e)$. A similarity of ratio $1/2$, with the height reflection
specified in `NOVELTY.md`, gives the target edge-two tetrahedron without
changing this ratio. The target's physical slope parameter is $\tau=2e$.

## 2. Roots at every closed-body point

Fix $(x,y,ht)\in K_c$. The source crossing lemma supplies
$p,q\in[-1,1]$ such that

$$
 y=(1-t)q-e xD(q),\qquad \rho=1-t+e xq\ge0,
$$

$$
 x=(1+t)p+e yD(p),\qquad \sigma=1+t-e yp\ge0.
$$

For completeness, the first root map is
$F(q)=(1-t)q-e xD(q)$. Its values at $-1,1$ are
$-(1-t),1-t$, which bracket $y$; its derivative is the displayed
$\rho$. A continuous differentiable function crossing upward through a
level has a root with nonnegative derivative, with one-sided derivatives
allowed at endpoints. The second map has endpoint values
$-(1+t),1+t$ bracketing $x$, and derivative $\sigma$.

This argument uses no division by $1-t$, $1+t$, $p$, or $q$.
It therefore includes $t=\pm1$, zero radial parameters, and angular
endpoints. If either radial parameter is zero, its sweep already covers the
point because the cap is positive. In general, rearranging gives

$$
 y=\rho q-e xG(q),\qquad x=\sigma p+e yG(p),\qquad
 \rho+\sigma=2+e(xq-yp).                                      \tag{1}
$$

The free-coordinate bounds $|x|,|y|\le2$ follow from $K_c$.
Only the upper radial bounds remain to be established.

## 3. Eliminate the spatial coordinates before estimating

Write $G_p=G(p)$, and similarly for other functions, and define

$$
 N=1+e^2G_pG_q,\quad
 A=1+epq+e^2G_pD_q,\quad B=1-epq+e^2G_qD_p.
$$

Solving the first two equations in (1) gives the exact formulas

$$
 x=\frac{\sigma p+e\rho qG_p}{N},\qquad
 y=\frac{\rho q-e\sigma pG_q}{N}.
$$

Substitution into the last equation in (1), using $G(r)-r^2=D(r)$,
gives

$$
 \boxed{A\rho+B\sigma=2N.}                                  \tag{2}
$$

For $0<e\le1$,

$$
 A,B\ge1-e\ge0,\qquad
 A+B=2+\frac{e^2}{2}(1-p^2q^2)\ge2.                           \tag{3}
$$

At $e=1$ one weight can vanish, but both cannot vanish. Consequently
simultaneous strict failures $\rho>R(q)$, $\sigma>R(p)$ imply

$$
 2N>AR(q)+BR(p).                                               \tag{4}
$$

It is enough to prove the reverse non-strict inequality for every
$p,q\in[-1,1]$. No estimate of $x-p$, $y-q$, or $t/e-pq$
is needed.

## 4. Complete the square

For the cap $R(r)=1+e^2H(r)+Ce^4$, set

$$
 d=p^2-q^2,\qquad s=p^2+q^2,\qquad
 T=G_pD_qH_q+G_qD_pH_p\ge0.
$$

The exact residual is

$$
\begin{aligned}
 AR(q)+BR(p)-2N
 &=\frac{e^2d^2}{2}+e^3pq(H_q-H_p)+e^4T+Ce^4(A+B)\\
 &=\frac{e^2}{2}\left(d-\frac{epq(1+s)}2\right)^2
   +e^4\left[T-\frac{p^2q^2(1+s)^2}{8}+C(A+B)\right].          \tag{5}
\end{aligned}
$$

Here $H_q-H_p=-d(1+s)/2$. Since
$p^2q^2\le1$, $1+s\le3$, and $A+B\ge2$, taking
$C=9/16$ makes the bracket nonnegative:

$$
 T-\frac{p^2q^2(1+s)^2}{8}+\frac9{16}(A+B)
 \ge 0-\frac98+\frac98=0.
$$

Thus the residual is nonnegative. This contradicts (4) and proves coverage.
Strict overlap is not required: the source sweeps include their radial
boundaries, so a point with $\rho=R(q)$ or $\sigma=R(p)$ is covered.

## 5. Sharpness of the constant within this family

Fix $C<9/16$. For small positive $e$, take

$$
 p=1,\qquad q=\sqrt{1-\frac32e},\qquad
 R(r)=1+e^2H(r)+Ce^4,
$$

and let $\Delta=AR(q)+BR(p)-2N$. In the first line of (5),
$d=3e/2$, $pq\to1$, $s\to2$, $T\to0$, and
$A+B\to2$. Therefore

$$
 \lim_{e\downarrow0}\frac{\Delta}{e^4}
 =\frac98-\frac94+2C=2C-\frac98<0.                            \tag{6}
$$

For all sufficiently small $e$, define

$$
 \delta=-\frac{\Delta}{A+B}>0,\qquad
 \rho=R(q)+\delta,\qquad \sigma=R(p)+\delta.
$$

Then (2) holds. Define $x,y$ by the exact inverse formulas in Section 3,
and set $t=1-\rho+e xq$. Reversing the algebra proves both equations
in (1) and both root equations. Because $p=1$, the second root equation
gives $x=1+t$. Moreover $x,y\to1$ and $t\to0$. Hence for small
$e$, $x,y>0$, $-1<t<1$, and

$$
 y=(1-t)q-e xD(q)\le1-t.
$$

Thus $(x,y,ht)\in K_c$, on its face $x=1+t$.

It remains to exclude another root that might cover this point. On the
whole angular interval the two root-map derivatives are bounded below by

$$
 1-t-e|x|\longrightarrow1,\qquad
 1+t-e|y|\longrightarrow1.
$$

They are positive for small $e$, so both roots are unique. Both unique
radial parameters strictly exceed their caps. The constructed point is
therefore outside both sweeps. This proves the asserted sharpness, rather
than merely failure of a sufficient algebraic test.

## 6. Limiting area, uniform error, and an explicit saving

Write $u=e^2$ and $C=9/16$. The Taylor expansion is uniform for
$-1\le r\le1$, because $0\le H(r)\le1$ and
$1/4\le D_0(r)\le3$. Its first terms are

$$
 Q(e)=1-\frac{e^2}{30}+\frac{929}{630}e^4+O(e^6).              \tag{7}
$$

The quadratic coefficient is the source's existing coefficient:
$\int_{-1}^1(H-D_0/4)=-1/30$. For the fourth-order coefficient,

$$
 \frac12\int_{-1}^1
 \left(H^2-HD_0+\frac38D_0^2\right)\,dr=\frac{881}{2520},
$$

and the constant correction contributes $2C=9/8$. Their sum is
$929/630$. Equivalently, the polynomial inside the last integral is

$$
 \frac{3+44r^2+162r^4-52r^6+19r^8}{128}.
$$

An explicit upper error bound avoids relying on the asymptotic notation.
For $v\ge0$, Taylor's theorem with a negative third derivative gives

$$
 (1+v)^{-1/2}\le1-\frac v2+\frac{3v^2}{8}.
$$

Multiply this inequality by
$R^2=1+2Hu+(H^2+2C)u^2+2CHu^3+C^2u^4$. The coefficients of
$u^3,u^4,u^5,u^6$ in the resulting upper polynomial are, pointwise,
at most

$$
 \frac{63}{8},\quad\frac{1917}{256},\quad
 \frac{243}{64},\quad\frac{2187}{2048}.                       \tag{8}
$$

Indeed their exact expressions are

$$
\begin{aligned}
 c_3&=\tfrac34HD_0^2-\tfrac12D_0(H^2+2C)+2CH,\\
 c_4&=\tfrac38D_0^2(H^2+2C)-CD_0H+C^2,\\
 c_5&=\tfrac34CHD_0^2-\tfrac12C^2D_0,\\
 c_6&=\tfrac38C^2D_0^2.
\end{aligned}
$$

Dropping their displayed negative terms and using $H\le1,D_0\le3$
proves (8). For $0\le u\le1/100$,

$$
 \frac{63}{8}+\frac{1917}{25600}
 +\frac{243}{640000}+\frac{2187}{2048000000}<8.
$$

The normalized integral $\tfrac12\int_{-1}^1$ preserves this bound,
so

$$
 \boxed{Q(e)\le1-\frac{e^2}{30}+\frac{929}{630}e^4+8e^6}
 \qquad(0\le e\le1/10).                                     \tag{9}
$$

In particular,

$$
 1-Q(1/10)\ge\frac{5603}{31500000}>\frac1{6000}.              \tag{10}
$$

Consequently the source's convergent finite triangle approximations,
after a sufficiently fine but not yet quantitatively specified partition,
have total area below half the minimum projection area. Inequality (10)
does not itself specify the number of cylinders. It gives an explicit
limiting gap available to a finite error estimate.

In the target normalization, (7) reads

$$
 \frac{\text{limiting total base area}}{A_{\min}}
 =\frac12-\frac{e^2}{60}+\frac{929}{1260}e^4+O(e^6)
 =\frac12-\frac{\tau^2}{240}
   +\frac{929}{20160}\tau^4+O(\tau^6).
$$

## 7. Optional profile, outside the primary theorem

A nonconstant fourth-order correction can reduce the fourth-order
limiting cost. This is a secondary observation, not the cap used in the
primary finite comparison. For $0<e<1$, put

$$
 \widetilde R_e(r)=1+e^2H(r)+\frac{9e^4}{16(1-e^2)}r^4.         \tag{11}
$$

Let $a=p^2,b=q^2,z=pq$. The correction in (5) becomes
$\frac{9e^4}{16(1-e^2)}(Ab^2+Ba^2)$. Since
$A\ge1+ez$, $B\ge1-ez$, weighted arithmetic-geometric mean gives

$$
 Ab^2+Ba^2\ge2ab\sqrt{1-e^2z^2}\ge2ab(1-e^2).
$$

Its contribution is at least $9e^4ab/8$, which dominates
$e^4ab(1+a+b)^2/8$. The same square-completion proof therefore gives
closed-body coverage. Its limiting cost is

$$
 \widetilde Q(e)=1-\frac{e^2}{30}+\frac{181}{315}e^4+O(e^6),
$$

because $\int_{-1}^1(9r^4/16)\,dr=9/40$ and
$881/2520+9/40=181/315$. No optimality is claimed for this profile.
No finite count or all-source comparison has been established for (11).

## 8. What is new, and what is inherited

The pinned radial
[`caps.tex`](../sources/Finite-triangular-approximation-of-radial-sweeps-September-27-2026/build/caps.tex)
already contains:

- Fixed $\beta>0$ linear caps $1+e^2(H+\beta)$, and square-root
  caps with the same quadratic coefficient.
- Cubic caps $1+e^2H+ce^3$, with every $c\ge9/2$ and coverage for
  every $e>0$, plus fractional padding.
- The exact identity `eq:weighted-radial-identity`, whose right side
  retains $x,y$, and the squared-radius identities.
- The sufficient common padding test
  $b_e(p)+b_e(q)\ge9e$ for $R=1+e^2(H+b_e)$.

The new estimate here eliminates $x,y$ exactly, keeps the positive
weights (2), and uses the factorization of $H_q-H_p$ to absorb the
cubic cross term into a square. This gives an explicit quartic certificate,
its sharp constant within a specified family, and a quantitative limiting
area bound.

At a single fixed tilt, the primary cap is syntactically an existing
linear cap with $\beta=(9/16)e^2$. It is therefore not a new algebraic
family of radial surfaces. The new conclusion is that this vanishing
choice is feasible uniformly on the explicit interval, where the source's
fixed-$\beta$ theorem and displayed common test do not imply it.
In fact the common test for this cap would require $e\ge8$, outside
the present interval.

The angular paper's
[`angular-extensions.tex`](../sources/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/build/sections/angular-extensions.tex),
Theorem `ext:general-cap`, assumes a fixed positive quadratic margin
$\eta$. Its threshold may depend on $\eta$. Substituting a margin
that tends to zero with the tilt is not justified by that theorem. The
angular paper explicitly treats cubic padding separately in
[`cubic-buffer.tex`](../sources/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/build/sections/cubic-buffer.tex).

One bounded comparison follows immediately. Setting $p=q$ in the
source's common padding test forces $b_e(r)\ge9e/2$ pointwise. For
every $0<e\le1$, the present constant correction
$(9/16)e^2$ is strictly smaller. Thus its cap and limiting cost are
strictly smaller than every cap certified by that common test at the same
tilt, with the same radial line families. This does not compare finite
approximations with different footprints, caps certified by different
arguments, compatible boundaries, shortened beams, rational slope fields,
or actual swept-projection bases. Those remain separate obligations.

The crossing lemma, closed-body root selection, tetrahedron projection
area, finite radial approximation theorem, and leading saving coefficient
are all inherited source results. This note does not claim their novelty.

## 9. Checks and limitations

After `NOVELTY.md` was present, one small exact checker using Python's
standard-library `fractions.Fraction` verified the completed-square
polynomial identity, the integrated upper polynomial, the bound in (9),
and the rational saving in (10). Its integrated coefficients, from
$u^0$ through $u^6$, were

$$
 1,\ -\frac1{30},\ \frac{929}{630},\
 \frac{265789}{720720},\ \frac{5802311}{5026560},\
 \frac{807549}{2562560},\ \frac{16497}{71680}.
$$

An initial attempted SymPy check stopped at import because SymPy is not
installed; no packages were installed. No floating-point point cloud,
optimization run, or numerical coverage experiment was used. The proofs
above are independent of the checker. The sharpness construction and the
optional profile are elementary analytical proofs, not computational claims.

This note establishes neither an optimal cap among all profiles nor
optimal finite cylinders. It supplies the cap part of the proposed finite
package. Independent integration review is still needed for physical
normalization, finite footprint formulas, count, and broader comparison.
