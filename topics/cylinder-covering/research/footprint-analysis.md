# Correlated frozen footprints and boundary coverage

Historical derivation note. The preliminary comparison gaps discussed below
were subsequently addressed by the compatible-secant construction and the
explicit source-range audit. For current results and scope, use
[SECANT-THEOREM.md](../SECANT-THEOREM.md), [RESULT.md](../RESULT.md), and
[published-proof-ranges.md](published-proof-ranges.md).
This note proves finite enclosures directly from the exact radial-sweep
intercept identity. It does not identify a finite enclosing triangle with
the actual projected sweep. Source references are the pinned radial
companion's `build/footprints.tex`, `build/freezing.tex`, and
`build/tetrahedron.tex`.

The simple triangle below is a source corollary: it is the triangle
obtained by extending the source's midpoint affine trapezoid with
$(A,B)=(\varepsilon,3\varepsilon/4)$ to the intersection of its
sloping sides. Its direct proof is included for a self-contained
certificate, not as a novelty claim. The sharper triangle additionally
uses the cap bound in its support slopes; its status in the complete
finite theorem is assessed by `NOVELTY.md`.

## Coordinates and hypotheses

Use the radial companion's edge-four tetrahedron

$$
K_4=\{(x,y,\sqrt2\,t): |x|\le1+t,\ |y|\le1-t\}.
$$

Let an upper sweep have parameters $q\in[-1,1]$,
$0\le\rho\le R(q)$, and $|x|\le2$, where $R$ is continuous
and nonnegative. Fix a closed interval $I=[c-a,c+a]$, where
$a=d/2>0$, and freeze its direction at the midpoint $c$. Put

$$
M=\max_I R,\qquad k=2\varepsilon,\qquad
e=q-c,\qquad s=\varepsilon x.
$$

Thus $|e|\le a$, $|s|\le k$, and $0\le\rho\le M$. Sliding
the sweep point to $x=0$ in the frozen direction gives

$$
u=\rho-se,\qquad W=Y-cu=e\rho-\frac{s e^2}{2}.             \tag{1}
$$

The physical intercept is $(0,cu+W,\sqrt2(1-u))$. Its area element
is $\sqrt2\,du\,dW$, and projection perpendicular to the frozen
direction $(1,-\varepsilon G(c),\sqrt2\varepsilon c)$ divides area
by

$$
\sqrt{1+\varepsilon^2D_0(c)},\qquad
G(c)=\frac{1+c^2}{2},\quad D_0(c)=G(c)^2+2c^2.             \tag{2}
$$

The affine shear from $(u,W)$ to $(u,Y)$ has determinant one.

## A smaller triangle valid for every positive mesh and tilt

Every intercept (1) belongs to the closed triangle

$$
T^{\rm simple}_I=
\left\{(u,W):
-\frac{3ka}{2}\le u\le M+ka,
\quad |W|\le a\left(u+\frac{3ka}{2}\right)\right\}.        \tag{3}
$$

Here is a direct support-line proof, retaining the correlation that is
lost if the two errors in (1) are bounded separately. Since $e-a\le0$,

$$
W-au=(e-a)\rho+s\left(ae-\frac{e^2}{2}\right)
\le k\max_{|e|\le a}\left|ae-\frac{e^2}{2}\right|
=\frac{3ka^2}{2}.                                      \tag{4}
$$

The last equality follows because $ae-e^2/2$ increases from
$-3a^2/2$ to $a^2/2$ on $[-a,a]$. Applying the same argument
to $(-e,-W)$, with the sign of $s$ reversed, gives
$-W-au\le3ka^2/2$. Also $u\le M+ka$. These three supporting
half-planes imply the lower bound in (3), so there is no extra
containment condition at its vertex. Both sloping support constants are
attained already at $\rho=0$, using endpoint values of $e$ and
$s$; the proof is valid for a variable cap and for $M=0$.

The three vertices, in $(u,W)$ coordinates, are

$$
\left(-\frac{3\varepsilon d}{2},0\right),\qquad
\left(M+\varepsilon d,
 \ \pm\frac d2\left(M+\frac{5\varepsilon d}{2}\right)\right).
                                                                    \tag{5}
$$

Consequently its exact coordinate area is

$$
|T^{\rm simple}_I|
=\frac d2\left(M+\frac52\varepsilon d\right)^2.           \tag{6}
$$

The source midpoint triangle has exact coordinate area
$d(M+4\varepsilon d)^2/2$. Equation (6) is strictly smaller whenever
$\varepsilon d>0$ and $M\ge0$. In fact (3) is contained in that
source triangle: its upper endpoint, lower endpoint, and half-width are
all smaller. This is a comparison of finite triangles for the same cap,
same interval, and same frozen direction.

For $\varepsilon>0$, $d>0$, the triangle is nondegenerate even
when $M=0$. At $\varepsilon=0$ it is the ordinary sector triangle
if $M>0$, and it degenerates to a point if $M=0$. Any theorem
requiring nondegenerate triangles should either state
$\varepsilon>0$ or handle that last zero-area case separately.

Projection multiplies (6) by (2)'s positive area factor, so the exact
perpendicular-base area is

$$
\frac{\sqrt2\,d}{2\sqrt{1+\varepsilon^2D_0(c)}}
\left(M+\frac52\varepsilon d\right)^2.                  \tag{7}
$$

Projection is injective on the intercept plane because the frozen
direction has first component one. It therefore preserves compactness,
nondegeneracy, and triangular shape.

## An optional sharper triangle when $\varepsilon d/M\le1/2$

Suppose $M>0$ and $M\ge2ka=2\varepsilon d$. Define

$$
z=\frac{ka}{M}=\frac{\varepsilon d}{M},\qquad
\ell=a(1-z),\qquad
V=ka+\frac{ka^2}{2\ell},\qquad U=M+ka.
$$

Then $a/2\le\ell<a$ for positive tilt. Another enclosing triangle is

$$
T^{\rm sharp}_I=\{(u,W): u\le U,\ |W|\le\ell(u+V)\}.    \tag{8}
$$

To prove it, fix $e,s$. Every supporting functional is affine in
$\rho$, so it is enough to prove its upper bound at $\rho=0,M$.
At $\rho=0$,

$$
u\ge-ka,\qquad |W|\le\frac{ka^2}{2},\qquad
W-\ell u\le\ell ka+\frac{ka^2}{2}=\ell V.               \tag{9}
$$

At $\rho=M$, the exact identity is

$$
W=\frac e2(M+u),\qquad M-ka\le u\le M+ka.
$$

Since $M+u>0$ and $\ell\ge a/2$,

$$
\begin{aligned}
W-\ell u
&\le\frac{aM}{2}+\left(\frac a2-\ell\right)u\\
&\le\frac{aM}{2}+\left(\frac a2-\ell\right)(M-ka)\\
&=(a-\ell)M+\ell ka-\frac{ka^2}{2}
 =\ell ka+\frac{ka^2}{2}=\ell V.                         \tag{10}
\end{aligned}
$$

The penultimate equality uses $(a-\ell)M=ka^2$. Symmetry gives the
lower sloping support bound, and $u\le U$ always holds. This is a
universal containment proof, not a check at sampled parameters.

The exact coordinate area can be written in either of two useful forms:

$$
\begin{aligned}
|T^{\rm sharp}_I|
&=\ell(U+V)^2\\
&=\frac{dM^2}{2}
  \frac{(1+\frac32z-2z^2)^2}{1-z}\\
&=\frac{dM^2}{2}
  \left(1+4z+\frac{z^2(\frac32-2z)^2}{1-z}\right).       \tag{11}
\end{aligned}
$$

For $0\le z\le1/2$ this gives the convenient bound

$$
|T^{\rm sharp}_I|\le\frac d2(M+2\varepsilon d)^2.        \tag{12}
$$

Indeed the difference between the bracket in the last line of (11) and
$(1+2z)^2$ is

$$
\frac{z^2(4z^2-2z-7/4)}{1-z}\le0.
$$

Both endpoints of the convex quadratic $4z^2-2z-7/4$ on
$[0,1/2]$ equal $-7/4$, so its value is at most $-7/4$
throughout that interval. The physical projection factor is again (2).
No optimality among all containing triangles is claimed.

For caps $R\ge1$, the condition for (8) holds for every interval of
any partition of $[-1,1]$ whenever $0<\varepsilon\le1/4$, because
$d\le2$ and $2\varepsilon d\le1\le M$. Thus it does not impose
an additional count condition in that small-tilt range.

## Exact convex hull for the constant-cap comparison set

This paragraph is a geometric check and an additional convex-base
formula; replacing (8) by this hexagon changes the permitted base class.
Let $S_M$ denote the intercept set (1) with the full constant cap
$0\le\rho\le M$, and assume $M>2ka>0$.

At $\rho=0$, its convex hull is exactly the rectangle with vertices
$(\pm ka,\pm ka^2/2)$. All four vertices are realized in (1).
At $\rho=M$, its convex hull is exactly the trapezoid with vertices

$$
\left(M-ka,\ \pm\left(aM-\frac{ka^2}{2}\right)\right),
\quad
\left(M+ka,\ \pm\left(aM+\frac{ka^2}{2}\right)\right).
$$

Containment follows from $|W|\le a(M+u)/2$; all four vertices are
again realized. For fixed $e,s$, intermediate values of $\rho$
are segments between these two endpoint sets. Therefore their combined
convex hull equals $\operatorname{conv}S_M$. The two right-hand
rectangle vertices lie below the sloping supports, leaving the six
vertices

$$
\left(-ka,\ \pm\frac{ka^2}{2}\right),\quad
\left(M-ka,\ \pm\left(aM-\frac{ka^2}{2}\right)\right),\quad
\left(M+ka,\ \pm\left(aM+\frac{ka^2}{2}\right)\right).    \tag{13}
$$

The upper boundary has slopes $\ell=a-ka^2/M$ and $a/2$, in
that order, so the displayed polygon is convex. Integrating its full
vertical width first over $[-ka,M-ka]$, then over
$[M-ka,M+ka]$, gives exactly

$$
|\operatorname{conv}S_M|
=aM^2+4ka^2M
=\frac{dM^2}{2}+2\varepsilon M d^2.                    \tag{14}
$$

At $M=2ka$, adjacent sloping edges merge and the same formula
holds for the resulting trapezoid. The sharp triangle's excess over
(14) is precisely

$$
\frac{dM^2}{2}\frac{z^2(\frac32-2z)^2}{1-z}\ge0.
$$

This proves exactness of the convex-hull formula for the declared
constant-cap comparison set. It does not prove a minimum-area triangle
theorem and does not assert that a variable-cap sweep has this hull.

## First-crossing lemma, endpoints, and zero radii

Let $F\in C^1([A,B])$, $A<B$, and suppose
$F(A)\le y\le F(B)$. There exists $r\in[A,B]$ with
$F(r)=y$ and $F'(r)\ge0$, using the derivative from within the
interval at an endpoint.

If $F(A)=y$ and $F'(A)\ge0$, take $r=A$. Otherwise choose
$A'\in[A,B)$ with $F(A')<y$: take $A'=A$ if the initial
inequality is strict, or use the negative right derivative if it is an
equality. The closed nonempty set
$\{t\in[A',B]:F(t)=y\}$ has a first point $r>A'$. Continuity
gives $F(t)<y$ for $A'\le t<r$. Thus every sufficiently short
left difference quotient at $r$ is nonnegative. Its limit is
$F'(r)\ge0$, including when $r=B$. A constant function presents
no exception: its derivative is zero.

For a point $(x,y,\sqrt2t)\in K_4$, apply this lemma to

$$
F(q)=(1-t)q-\frac{\varepsilon x}{2}(1-q^2),\qquad
J(p)=(1+t)p+\frac{\varepsilon y}{2}(1-p^2).
$$

The endpoint values are respectively $\pm(1-t)$ and
$\pm(1+t)$, which bracket $y$ and $x$. The resulting roots
satisfy

$$
\rho=F'(q)=1-t+\varepsilon xq\ge0,
\qquad
\sigma=J'(p)=1+t-\varepsilon yp\ge0.                    \tag{15}
$$

No monotonicity assumption on all of either quadratic is needed. The
two choices can be made independently. At $t=1$, $y=0$, a root
$q=\operatorname{sgn}x$ gives $\rho=\varepsilon|x|$; if
$x=0$, any $q$ gives $\rho=0$. At $t=-1$, $x=0$,
take $p=-\operatorname{sgn}y$ to obtain
$\sigma=\varepsilon|y|$, with the analogous all-zero exception.
These examples illustrate the endpoint derivatives used by the proof;
the general lemma already covers them.

Rearranging the root equations gives the actual upper and lower sweep
representations. If $\rho=0$ (respectively $\sigma=0$), the
selected representation automatically satisfies any nonnegative cap in
that family. Thus a proof by contradiction from simultaneous cap failure
may assume both radii are strictly positive. No division by a selected
radius is required either here or in (3), (8).

For a finite partition, each angular root belongs to at least one
closed interval. At a shared endpoint it may belong to both; either
enclosing triangle works because the proofs use non-strict parameter
bounds. There is no gap between adjacent sectors and no need for a
unique sector-selection convention.

Whenever a separate cap-overlap argument proves that the two sweeps
cover $K_4$, projecting one enclosing triangle for each of $N$
intervals and reflecting the upper family by
$\mathcal R(x,y,z)=(y,-x,-z)$ supplies exactly $2N$ labeled
cylinders. The map is orthogonal, preserves $K_4$, and preserves base
areas and shapes. All are closed infinite cylinders over compact
triangles, and they cover every point of the closed tetrahedron.

## Relation to the user's physical normalization

The user's tetrahedron is

$$
K=\{(X,Y,\sqrt2S): 0\le S\le1,\ |X|\le1-S,\ |Y|\le S\}.
$$

The similarity

$$
(x,y,\sqrt2t)\longmapsto
\left(\frac y2,\frac x2,\frac{\sqrt2(t+1)}2\right)
$$

takes $K_4$ onto $K$. All base and projection areas are divided
by four, so normalized total cost is unchanged. In particular,
$A_{\min}(K_4)=4\sqrt2$ becomes $A_{\min}(K)=\sqrt2$.
For an equal partition with $d=2/N$, the two-family simple-triangle
normalized cost is exactly

$$
\mathcal R^{\rm simple}_{N,\varepsilon}
=\frac d4\sum_{j=1}^N
\frac{(M_j+\frac52\varepsilon d)^2}
     {\sqrt{1+\varepsilon^2D_0(c_j)}}.                  \tag{16}
$$

For the sharp triangle, replace the squared term in (16) by
$M_j^2(1+\frac32z_j-2z_j^2)^2/(1-z_j)$, where
$z_j=\varepsilon d/M_j$. Equation (12) supplies the rigorous upper
bound obtained by replacing it with $(M_j+2\varepsilon d)^2$.
Any comparison with a tilt named $\tau$ elsewhere must separately
identify its frozen direction under this similarity; no parameter
rename is part of the footprint improvement.

## BASELINE LIMITATIONS

This adversarial audit distinguishes comparison of certified bounds from
a lower bound on every possible finite implementation of a source
method. The latter has not been proved. In particular, unspecified
finite counts and unspecified small-parameter thresholds are unresolved
comparisons, not evidence that a source construction is inferior.

**Physical tilt.** For the present midpoint axes the tangent of the
deviation from the corresponding equality-cover axis is
$\varepsilon\sqrt{D_0(c)}$. On an equal $N$-partition its maximum
is attained at $|c|=1-1/N$, and it is at most
$\sqrt3\varepsilon$. The main angular source at $\tau=2\varepsilon$
uses secant directions with tangent

$$
\varepsilon\sqrt{\left(G(c)-\frac{1}{2N^2}\right)^2+2c^2}.
$$

Thus both satisfy the same physical tilt envelope, but their exact
finite maximum angles differ. A claim requiring equality of those
maximum angles must make that additional adjustment rather than rely
only on the symbol dictionary $\tau=2\varepsilon$.

**Angular fixed margins.** The main source's compatible-cap theorem
allows every fixed $0<\eta<1/480$, with normalized cost
$1/2+(2\eta-1/240)\tau^2+O(\tau^4)$, uniformly over its permitted
finer meshes. Its tilt threshold and remainder constant can depend on
$\eta$. This includes triangular midpoint and maximum caps, as well
as continuous, squared-radius and Cartesian apertures. Any one fixed
positive margin is asymptotically worse than a vanishing-margin theorem
with the full quadratic coefficient, but this fact gives no uniform
comparison over all choices of $\eta$ at a specified positive tilt.
Failure of a sufficient coverage budget does not prove that those
actual covers fail. In particular, no conclusion at
$\varepsilon=1/10,N=10000$ follows from their asymptotic formula
alone. The node-centred specialization also has only an unspecified
sufficiently-large-integer threshold.

**Rational slope fields.** The slope-field source's rational family
fixes a smoothing parameter $d>0$, then padding and a small tilt
$\epsilon_{\rm rat}$, and finally finite approximation tolerances.
It supplies no uniform cylinder-count bound. Its normalized total
weighted cost is
$1/2+4\epsilon_{\rm rat}^2(J_d-I_d)+2q+O(\epsilon_{\rm rat}^4)$.
On a wedge label with radial coordinate $r$, the greatest physical
velocity norm at that radius is attained on its walls and equals
$\sqrt3\,r/[8(r+d)]$. Hence its maximum physical axis-deviation
tangent on the full label set is

$$
\frac{\sqrt3\epsilon_{\rm rat}}8\frac{r_{\max}}{r_{\max}+d}.
$$

In particular, simply taking $\epsilon_{\rm rat}=8\varepsilon$
does not exactly match physical tilt when $d>0$. At leading order
$r_{\max}\to1/2$, so the matched-tilt saving depends on
$(I_d-J_d)(1+2d)^2$. The source gives its limit as $d\downarrow0$,
not a global optimality theorem in $d$. No universal finite-budget
dominance over this family has been established here.

**Singular slope fields.** For each fixed allowed $p>1$, its
edge-two directions have maximum deviation tangent
$(\sqrt3/2)c(1+O(c^2))$. With $c=2\varepsilon$ at leading order,
the normalized quadratic coefficient is

$$
8\kappa_p=\frac{2p^2+10p-13}{60p}>-\frac1{60},
$$

because $2p+10-13/p$ is strictly increasing for $p>0$.
Thus every fixed such exponent has a weaker leading saving. This is
not a bound uniform as $p\downarrow1$; the cutoff, coverage and
approximation estimates are stated with $p$ fixed. The source gives
two additional triangular tip cylinders, but no uniform count for its
main parallelogram families. This remains an unresolved finite-budget
comparison rather than a proved inferior cover at a specified tilt.

**Square-zero angular field.** Its source parameter $k=2\varepsilon$
matches the continuous radial directions exactly. The source's cap
becomes
$1+\varepsilon^2H+16\varepsilon^3$ in canonical coordinates. Its
advertised limiting cost therefore exceeds the radial cubic cap with
coefficient $9/2$. At $\varepsilon=1/10$, that limiting cost is
at least

$$
\frac{(1+16\varepsilon^3)^2}{2\sqrt{1+3\varepsilon^2}}
>\frac12.
$$

The last inequality follows by squaring and using
$(127/125)^4>103/100$. This compares the stated weighted cost, not
every possible realization by the general approximation theorem. The
source gives an explicit apex-net count but only an existential finite
count for the remaining square tiles.

**Shortened beams and strip.** The radial source's beam construction
uses a different pair of equality axes. With $\beta=1/\sqrt2$, their
unit representatives are
$b_\pm=(\pm\beta,\mp\beta,1)/\sqrt2$. Every horizontal strip
axis can be written
$s=(1-v,-1-v,0)/\sqrt{2+2v^2}$. Hence
$|s\cdot b_\pm|=1/\sqrt{2+2v^2}\le1/\sqrt2$: each strip axis
makes an unoriented angle at least $\pi/4$ with either corresponding
equality axis. This is outside the present all-axis envelope
$\arctan(\sqrt3/10)<\pi/4$, after any isometry aligning the equality
pair. It is excluded by that declared tilt resource, not proved
inferior in area. Its bases also mix triangles with rectangles and its
strip count is only implicit. Allowing arbitrary axes or mixed bases
would reopen that comparison.

**Novelty challenge.** The pinned radial cap appendix already contains
the positive-weight identity
$(1+\varepsilon pq)\rho+(1-\varepsilon pq)\sigma
=2+\varepsilon^2\{qG(p)y+pG(q)x\}$, complementary-coordinate
identities, and exact squared-radius identities. The square-surplus
mechanism is also explicit in the rational and singular slope-field
proofs. Those ingredients should be credited. Reading these sections
and searching the complete pinned source tree found neither the
$9/16$ quartic radial certificate nor the exact identity after
eliminating both spatial coordinates. This is bounded prior-art
evidence, not proof of originality. For each fixed tilt, the new
polynomial cap is also algebraically a member of the source's linear
cap family with $\beta=(9/16)\varepsilon^2$; the candidate advance
is its uniform coverage and finite quantitative package, not a new
algebraic cap shape.

Finally, the source explicitly permits actual swept-projection bases,
which are contained in any enclosing triangles for the same sweeps and
directions. A triangle-only comparison must disclose that base-class
restriction. It cannot imply an optimum over all compact measurable
bases. None of the preceding audits closes the requested comparison
against every source construction at the same finite resource budget.
