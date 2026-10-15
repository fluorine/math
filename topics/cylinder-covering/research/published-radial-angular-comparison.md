# Published radial and angular comparisons

This note compares the published constructions on their proved parameter
ranges. It does not include every later admissible use of the generic
approximation methods. All costs are divided by the minimum projection area
of the edge-two target tetrahedron. The actual finite angle budget means
the largest angle of any axis from its corresponding opposite-edge direction.

The current construction has 20000 cylinders, canonical tilt $e=1/10$,
and certified cost

$$
 0.499947504745824\le R_{\rm new}\le0.499947504745984.
$$

Its finite maximum tangent is less than $\sqrt3/10$. The numerical
certificate is taken from the independent verifier, not recomputed here.

## 1. Arbitrary radial partitions and tags: an area lemma

Use the pinned radial manuscript's canonical coordinates, and write

$$
 G(q)=(1+q^2)/2,\quad H(q)=q^2G(q),\quad
 D_0(q)=G(q)^2+2q^2,\quad g_e(q)=(1+e^2D_0(q))^{-1/2}.
$$

Let $I=[l,r]$, $d=r-l>0$, and choose any tag $c\in I$. For a
continuous cap $R$, the actual frozen intercept set contains all points

$$
 u=\rho-s(q-c),\qquad
 Y=qu+\frac{s}{2}(q-c)^2,
 \quad q\in I,\ 0\le\rho\le R(q),\ |s|\le2e.                 \tag{1}
$$

This is the source's `eq:quadratic-foot-identity`, with $s=ex$.
Coordinate area is multiplied by $\sqrt2 g_e(c)$ in the canonical
perpendicular plane. The subsequent similarity divides physical area by
four. Denote the coordinate intercept set by $S_I$.

**Lemma.** If $0<e\le1/8$ and $1\le R(q)\le2$ on $[-1,1]$,
then

$$
 g_e(c)|S_I|\ge\frac12\int_I R(q)^2g_e(q)\,dq
 +\frac{29}{256}e\bigl((c-l)^2+(r-c)^2\bigr).                \tag{2}
$$

The estimate applies to actual projections; no convexity assumption is
made. In particular, after summing and including both families, every
finite source cover of these sweeps has cost at least

$$
 J_R(e)=\frac14\int_{-1}^1R(q)^2g_e(q)\,dq,                  \tag{3}
$$

for arbitrary partitions, arbitrary tags, and arbitrary numbers of intervals.
Every published enclosing footprint has at least the actual-base cost.

**Proof.** The slice $s=0$ contains the sector
$E_I=\{(u,Y)=(\rho,q\rho):q\in I,0\le\rho\le R(q)\}$, of
coordinate area $\frac12\int_I R^2$.

At the left endpoint $q=l$, additionally take the rectangle of parameters

$$
 -2e\le s\le0,\qquad 2e(c-l)\le\rho\le R(l).
$$

Its image in (1) has $u\ge0$ and
$Y-lu=s(l-c)^2/2\le0$. It therefore lies outside the sector's left
side, except for zero-area boundaries. The affine map $(\rho,s)\mapsto
(u,Y)$ has absolute determinant $(l-c)^2/2$, so this extra area is

$$
 e(c-l)^2\bigl(R(l)-2e(c-l)\bigr).
$$

Similarly, use $q=r$, $0\le s\le2e$, and
$2e(r-c)\le\rho\le R(r)$. Its image has $u\ge0$ and
$Y-ru\ge0$, so it lies outside the right side, with area

$$
 e(r-c)^2\bigl(R(r)-2e(r-c)\bigr).
$$

The parameter ranges are nonempty because $2ed\le1/2\le R$.
The two extra pieces and the sector have pairwise disjoint interiors.
If the tag equals an endpoint, that endpoint's zero-area piece is simply
omitted. Consequently, with $S_2=(c-l)^2+(r-c)^2$,

$$
 |S_I|\ge\frac12\int_I R^2+e(1-4e)S_2.                     \tag{4}
$$

On the whole angular range, $|g_e'|\le3e^2$. Since $R\le2$, the
possible error caused by freezing the projection weight at the tag is at most

$$
 \frac12\int_I R(q)^2|g_e(c)-g_e(q)|\,dq
 \le3e^2S_2\le\frac38 eS_2.                                \tag{5}
$$

Also $g_e(c)\ge1-3e^2/2\ge125/128$, and $1-4e\ge1/2$.
Thus the projected extra area in (4) is at least $125eS_2/256$.
Subtracting (5) leaves $29eS_2/256$, proving (2).

The normalized contribution of one physical family is
$\frac14\sum_I g_e(c)|S_I|$; applying (2) to both families proves
(3). They may even use different partitions and tags. For identical
partitions with $N$ intervals, Cauchy's inequality gives the additional
finite surplus $29e/(256N)$, although it is not needed below.

## 2. A global radial floor under the actual angle budget

The source's common padding criterion requires
$b_e(p)+b_e(q)\ge9e$ for the cap $1+e^2(H+b_e)$. Taking $p=q$
shows pointwise domination of

$$
 B_e(q)=1+e^2H(q)+\frac92e^3.                                \tag{6}
$$

This includes every published cubic constant $c\ge9/2$, and every other
published cap whenever its effective padding satisfies that criterion.
Fix the actual all-axis tangent budget

$$
 T_*\le\frac{\sqrt3}{10}.                                   \tag{7}
$$

The source is allowed to choose its own tilt $e'>0$, its partition,
its tags, and its count. It need not use $e'=1/10$. Every such cover
under (7) satisfies

$$
 \boxed{R_{\rm source}\ge\frac12-\frac1{23328000}
       >0.49999995>R_{\rm new}.}                             \tag{8}
$$

In particular, this is a same-budget comparison at 20000 cylinders; the
lower bound even permits the source any finite count.

For $0<e'\le1/8$, the baseline cap in (6) lies between 1 and
$1049/1024<2$, so (3) applies. Using
$(1+v)^{-1/2}\ge1-v/2$, $B_{e'}^2\ge1+2e'^2H+9e'^3$, and
the positive factor $1-e'^2D_0/2$, gives

$$
 J_B(e')\ge\frac12-\frac{e'^2}{60}+\frac92e'^3
                 -\frac32e'^4-\frac{51}{20}e'^5
 \ge\frac12-\frac{e'^2}{60}+4e'^3.                           \tag{9}
$$

Here $\int HD_0\le6$ and $\int D_0=34/15$. The last inequality
follows from $9/2-(3/2)e'-(51/20)e'^2\ge4$ on $[0,1/8]$.
The cubic polynomial $-x^2/60+4x^3$ has its global minimum on
$[0,\infty)$ at $x=1/360$, with value $-1/23328000$.

For $e'\ge1/8$, use the zero-free-coordinate sector only. The actual
angle budget implies every frozen projection factor is at least
$(1+3/100)^{-1/2}>197/200$, regardless of the tag or $e'$. Thus

$$
 R_{\rm source}\ge\frac{197}{200}
   \left(\frac12+\frac4{15}e'^2+\frac92e'^3\right)
 \ge\frac{1552163}{3072000}>\frac12.                         \tag{10}
$$

The right side is increasing in $e'$. This proves (8) without
equating a named tilt parameter with the actual finite maximum angle.

At the particular common tilt $e'=1/10$, (9) also yields the stronger
count-independent and tag-independent bound

$$
 R_{\rm source}\ge\frac{3024947}{6000000}
 =0.5041578333\ldots.                                        \tag{11}
$$

### Published fixed and fractional radial caps

The following are explicit sufficient subranges of the source's criterion,
not assertions that these ranges are maximal:

| Published cap | Explicit criterion-certified range |
|---|---|
| $1+e^2(H+\beta)$, $\beta>0$ | $e\le2\beta/9$ |
| $1+e^2H+ce^{5/2}$, $c>0$ | $e\le4c^2/81$ |
| $\sqrt{1+2e^2(H+\beta)}$, $\beta>0$ | $e\le\min(\beta,1/60)/5$ |

For the square-root row with $0<\beta\le1/60$, its exact effective
padding obeys
$b_e\ge\beta-e^2(1+\beta)^2/2$; the displayed range makes
$2b_e\ge9e$. Larger $\beta$ are included by monotonicity of the cap.
Hence every fixed positive published parameter eventually enters a range
covered by the global floor (8). This statement does not turn an unknown
larger existential coverage interval into an explicit one.

For reference, at the same canonical tilt and count
$N=\lceil2/e^2\rceil$, the linear and square-root caps, with any
$0<\beta\le1/60$, satisfy the arbitrary-partition lower bound

$$
 R_{L,S}\ge\frac12-\frac{e^2}{60}+\beta e^2
           -\left(\frac{83}{315}+\frac{17\beta}{30}\right)e^4
 \qquad(0<e\le1/8).                                         \tag{12}
$$

This follows from (3), $R_L^2\ge R_S^2=1+2e^2(H+\beta)$, and
$\int HD_0=332/315$. Combining (12) with the current new bound
$1/2-e^2/60+2e^3+(5/2)e^4$ gives strict familywise dominance for
all sufficiently small $e$, for example $e\le\beta/4$.
Only source tilts already covered by a source theorem or sufficient
criterion are being compared; the lower area inequality itself does not
establish coverage.

## 3. Angular maximum caps under the explicit coverage budget

Use the angular paper's physical tilt $\tau$. On a secant interval
$I_j=[l_j,r_j]$, set

$$
 \alpha_j=(1+l_jr_j)/4,\quad \beta_j=(l_j+r_j)/4,\quad
 A_j=\alpha_j^2+2\beta_j^2,\quad d(q)=(q^2+q^4)/16.
$$

For maximum caps $S_j=1/2+\tau^2(\eta+\max_{I_j}d)$, the exact
published area formula is

$$
 R_{\rm ang}=\sum_j|I_j|S_j^2(1+\tau^2A_j)^{-1/2}.            \tag{13}
$$

Write $A(q)=(1+q^2)^2/16+q^2/2$. If $m_j$ is the midpoint,
then $A_j\le A(m_j)$, and $A$ is convex. Consequently, for any
partition, not just equal intervals,

$$
 \sum_j|I_j|A_j\le\int_{-1}^1A(q)\,dq=\frac{17}{30}.         \tag{14}
$$

Also $0\le A_j\le3/4$. Using $S_j^2\ge1/4+\tau^2(\eta+d(q))$
and the positive lower projection factor $1-\tau^2A_j/2$ gives, for
$0<\tau<1$,

$$
 R_{\rm ang}\ge\frac12-\frac{\tau^2}{240}
 +\eta\tau^2\left(2-\frac34\tau^2\right)-\frac{\tau^4}{40}. \tag{15}
$$

The published quantitative coverage criterion, on its stated equal meshes
$2/N\le\tau^2$, is

$$
 2\eta-(2+2\eta)\tau-\tau^2/4\ge0.
$$

It forces $\eta\ge\tau/(1-\tau)\ge\tau$. Substituting in (15)
and using $0<\tau<1$ gives

$$
 R_{\rm ang}\ge\frac12-\frac{\tau^2}{240}+\tau^3
 \ge\boxed{\frac12-\frac1{93312000}}.                        \tag{16}
$$

The last minimum occurs at $\tau=1/360$. This is a global actual-cost
lower bound for every parameter choice certified by that explicit source
budget, with any permitted finite count. No angle-budget restriction is
needed for (16). It includes the original fixed-margin main construction
on its proved range.

The published angular cubic construction has $\eta=25\tau/4$ and
$N=\lceil8/\tau^2\rceil$. It satisfies the budget for
$0<\tau\le1/2$, so (16) applies. For $1/2\le\tau\le1$, its
caps are at least $41/32$ and its projection factors exceed $1/2$,
giving cost at least $(41/32)^2>1/2$. Thus the entire published
cubic range also lies above the new numerical result, regardless of count.

## 4. Fixed-positive-margin compatible angular families

The source compatible-cap theorem assumes a fixed
$0<\eta<1/480$, with uniform coefficient and cap errors, and proves

$$
 R_{\rm old}(\tau)=\frac12+
       \left(2\eta-\frac1{240}\right)\tau^2+O(\tau^4).        \tag{17}
$$

Both the threshold and the error constant may depend on the chosen family.
Its coefficient hypotheses force mesh $O(\tau^2)$, hence
$N(\tau)\ge\kappa/\tau^2$ for some fixed $\kappa>0$. They also
imply that the actual finite maximum tangent $T(\tau)$ satisfies

$$
 \left|T(\tau)-\frac{\sqrt3}{2}\tau\right|\le L\tau^3        \tag{18}
$$

for a fixed $L$. The lower estimate follows by evaluating the outer
cell's coefficient approximation at the endpoint $q=1$; the upper
estimate follows from the same uniform approximation on every cell.

**Familywise same-count, same-maximum-angle conclusion.** For each fixed
published compatible family with its fixed positive $\eta$, the new
triangles give a strictly cheaper cover for all sufficiently small admissible
$\tau$, with exactly the same $2N(\tau)$ count and exactly the same
finite maximum axis angle. This is not a statement uniform in
$\eta\downarrow0$.

Here is an explicit threshold in terms of the family's uniform constants.
Suppose its published valid interval also has the lower area estimate

$$
 R_{\rm old}(\tau)\ge\frac12-\frac{\tau^2}{240}
                         +2\eta\tau^2-K\tau^4.             \tag{19}
$$

Take $N=N(\tau)$, $c_N=1-1/N$, and set the new canonical tilt to

$$
 e_* =\frac{T(\tau)}{\sqrt{D_0(c_N)}}.                        \tag{20}
$$

Since the new midpoint grid's maximum $|q|$ is $c_N$, (20) matches
the actual maximum tangent exactly. Put

$$
 \lambda=2L/\sqrt3,\quad a=\lambda+2/\kappa,
$$

$$
 K_* =\frac a{40}+\frac{929}{1260}+\frac1{25}
                  +\frac{1681}{200\kappa}+\frac{2}{25\kappa^2}.
$$

If $\tau\le1/10$, $\tau^2\le\kappa/4$, and
$a\tau^2\le1/2$, then
$|e_* -\tau/2|\le a\tau^3$ and $e_*\le\tau$.
Indeed $|\sqrt{D_0(c_N)}/\sqrt3-1|\le2/N$; divide the two relative
errors in (18),(20), using $1-2/N\ge1/2$.

Substituting these bounds and $1/N\le\tau^2/\kappa$ in the new
uniform finite inequality gives

$$
 R_{\rm new}(e_*,N)\le\frac12-\frac{\tau^2}{240}
                          +\frac4\kappa\tau^3+K_*\tau^4.    \tag{21}
$$

Therefore the additional conditions

$$
 \tau\le\frac{\kappa\eta}{4},\qquad
 \tau^2\le\frac{\eta}{2(K+K_*)}                              \tag{22}
$$

give $R_{\rm old}-R_{\rm new}\ge\eta\tau^2/2>0$. All these
conditions must be intersected with the source family's own valid
coverage interval. If the source leaves that interval existential, (22)
does not supply its missing endpoint. It supplies an explicit cost-comparison
threshold once the source's uniform constants and valid interval are given.

### Constants for the displayed ordinary secant families

If the ordinary secant mesh obeys $\Delta\le M\tau^2$, take
$\kappa=2/M$ and $L=\sqrt3M/4$. The latter follows from the
outer cell: its coefficient norm is
$(\sqrt3/2)(1-|I_{\rm outer}|/2)$, while every coefficient norm is at
most $\sqrt3/2$.

For the source's maximum, continuous, and squared-radius caps, (19) holds
with $K=17/640$; the bounded Cartesian cap has the same lower bound
on its source-valid small-tilt branch. For midpoint caps it holds with
$K=3M/8+17/640$. To verify these constants, use (14),
$A_j\le3/4$, and $\int(d+\eta)\le17/240$. The negative product
term is at most $17\tau^4/640$. Only the midpoint cap needs the
additional replacement error $3\tau^2\Delta/8$, from
$|d'|\le3/8$. For the Cartesian cap, its source-valid root has
$S\ge1/2+\tau^2(d(q)+\eta)$, by monotonicity of its defining
transverse polynomial for $S\ge1/2$.

This covers all ordinary secant rows in the source's scaling table after
using their physical tilt dictionaries and exact counts. Their respective
mesh constants $M$ can be chosen as
$1/4,2,2,1,1/2,32,4\sqrt2,8$, in table order. Similarity does not
change normalized area or the count.

The displayed node-centered family has $N=k^2+1$, $\tau=1/k$,
$\eta=1/1000$, and actual maximum tangent exactly
$\sqrt3\tau/2$. One can take $\kappa=1,L=0,K=737/640$: the
node distance is at most $\tau^2$, so cap and projection replacement
errors are bounded by $3\tau^4/4$ and $3\tau^4/8$, respectively,
and the product term contributes at most $17\tau^4/640$.

## 5. A formerly conditional candidate, now certified by the new proof

This section records the adversarial area calculation that motivated the
new secant certificate. Its coverage question is now resolved positively in
[SECANT-THEOREM.md](../SECANT-THEOREM.md), Section 6. The source proof-range
audit is in [published-proof-ranges.md](published-proof-ranges.md).
Consider the published
continuous angular cap formula with

$$
 \eta=1/1000,\quad \tau=1/5,\quad N=10000,\quad
 S(q)=1/2+\tau^2(d(q)+\eta).
$$

Its exact finite **area**, whether or not it covers, is smaller than the
earlier radial frozen-triangle area:

$$
 R_{\rm candidate}<0.499937<0.499947504745824.                 \tag{23}
$$

Here is a conservative analytic certificate for (23). The corresponding
continuous radial cap is linear with $e=1/10$ and
$\beta=8\eta=1/125$. Expanding the inverse-square-root upper bound
gives

$$
 J_L\le\frac12+(\beta-1/60)e^2
 +\frac12\left(\frac{881}{2520}-\frac35\beta+\beta^2\right)e^4
 +\frac72e^6.
$$

For this $\beta$, the fourth-order bracket is below $7/20$, so
$J_L\le1/2-13/150000+7/400000+7/2000000
=0.4999343333\ldots$. The remainder bound follows from
$H+\beta\le1.008$, $D_0\le3$: the above-degree-two coefficients
of the upper polynomial are bounded by $(27/4)(1.008)$ and
$(27/8)(1.008)^2$, whose weighted sum is less than 7 for $e^2\le1/100$.

The secant weights differ from the continuous weights by at most
$\tau^2\Delta/2$, where $\Delta=1/5000$, because
$|A_j-A(q)|\le\Delta$. Since $S(q)\le0.50504$, the total
area discrepancy is at most $0.50504^2\tau^2\Delta<0.000002056$.
This proves (23). Its largest axis tangent is also below the common
budget $\sqrt3/10$.

**Coverage at $\tau=1/5$ is supplied by the new quartic/secant theorem.**
The source's own explicit thresholds do not certify this parameter choice.
The new padding is less than 19/800000, exactly the cap excess above the
quartic cap, so the simultaneous-failure proof now establishes full closed-body
coverage. This is a new feasibility-range result. It must not be relabeled as
a competitor already certified on the source's earlier numerical ranges.

No numerical coverage sampling is used. The arbitrary-tag lemma and both
global floors are exact geometric and algebraic proofs. The familywise result
retains its stated quantifiers. Separately, the later explicit source-witness
audit proves the one-point comparison on the identified published sufficient
ranges; see published-proof-ranges.md. Neither result excludes larger valid
ranges established by new proofs.
