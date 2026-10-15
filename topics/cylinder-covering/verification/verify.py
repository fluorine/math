#!/usr/bin/env python3
"""Independent rational certificates; run with Python 3, no dependencies.

The acceptance identities below reconstruct the sweep and support equations.
The constructor is imported only for a separate output-regression check.
Finite sums use exact power sums, so runtime does not grow with N.
"""

from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from math import comb, isqrt
from pathlib import Path


class Poly:
    """Sparse rational polynomial; deliberately small and self-contained."""

    def __init__(self, dim, terms=None):
        self.dim = dim
        self.terms = {k: F(v) for k, v in (terms or {}).items() if v}

    @classmethod
    def constant(cls, dim, value):
        return cls(dim, {(0,)*dim: F(value)})

    @classmethod
    def variable(cls, dim, index):
        powers = [0]*dim
        powers[index] = 1
        return cls(dim, {tuple(powers): F(1)})

    def coerce(self, value):
        if isinstance(value, Poly):
            assert value.dim == self.dim
            return value
        return self.constant(self.dim, value)

    def __add__(self, other):
        terms = dict(self.terms)
        for power, coefficient in self.coerce(other).terms.items():
            terms[power] = terms.get(power, 0) + coefficient
        return Poly(self.dim, terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.dim, {k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        terms = {}
        for p, a in self.terms.items():
            for q, b in self.coerce(other).terms.items():
                power = tuple(x+y for x, y in zip(p, q))
                terms[power] = terms.get(power, 0) + a*b
        return Poly(self.dim, terms)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (F(1)/scalar)

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = self.constant(self.dim, 1)
        for _ in range(exponent):
            result = result*self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def value(self, *values):
        assert len(values) == self.dim
        total = F(0)
        for powers, coefficient in self.terms.items():
            for x, exponent in zip(values, powers):
                coefficient *= x**exponent
            total += coefficient
        return total

    def compose(self, argument):
        assert self.dim == 1
        return sum((v*argument**k[0] for k, v in self.terms.items()),
                   Poly.constant(argument.dim, 0))

    def primitive(self):
        assert self.dim == 1
        return Poly(1, {(k[0]+1,): v/F(k[0]+1) for k, v in self.terms.items()})

    def integral(self, left=-1, right=1):
        p = self.primitive()
        return p.value(F(right)) - p.value(F(left))


def G(q):
    return (1+q*q)/2


def H(q):
    return q*q*G(q)


def D(q):
    return G(q)**2 + 2*q*q


def cap(e, q):
    return 1+e*e*H(q)+F(9, 16)*e**4


def check_cap_identity():
    e, p, q, rho, sigma = [Poly.variable(5, j) for j in range(5)]
    gp, gq = G(p), G(q)
    dp, dq = (1-p*p)/2, (1-q*q)/2
    denominator = 1+e*e*gp*gq
    # Reconstruct x,y from y=rho*q-e*x*G(q), x=sigma*p+e*y*G(p).
    xn = sigma*p + e*rho*q*gp
    yn = rho*q - e*sigma*p*gq
    assert yn-rho*q*denominator+e*xn*gq == 0
    assert xn-sigma*p*denominator-e*yn*gp == 0
    wq = 1+e*p*q+e*e*gp*dq
    wp = 1-e*p*q+e*e*gq*dp
    assert (denominator*(rho+sigma-2)-e*(xn*q-yn*p)
            == wq*rho+wp*sigma-2*denominator)
    delta, s = p*p-q*q, 1+p*p+q*q
    excess = wq*cap(e, q)+wp*cap(e, p)-2*denominator
    certificate = (e*e/2*(delta-e*p*q*s/2)**2
                   + e**4*(gp*gq*(p*p*dp+q*q*dq)
                           +(9-p*p*q*q*s*s)/8)
                   + F(9, 16)*e**6*(gp*dq+gq*dp))
    assert excess == certificate
    # Explicit nonnegative decomposition on |p|,|q|<=1.
    assert (9-p*p*q*q*s*s
            == 9*((1-p*p)+p*p*(1-q*q))
            + p*p*q*q*((1-p*p)+(1-q*q))*(3+s))
    # For 0<=e<=1, wq,wp >=1-e>=0 and their sum >=2.
    assert wq+wp == 2+e*e*(gp*dq+gq*dp)


def check_triangle_identities():
    z = Poly.variable(1, 0)
    assert ((1+F(3, 2)*z-2*z*z)**2
            == (1-z)*(1+4*z)+z*z*(F(3, 2)-2*z)**2)
    assert 4*(1-z)-(F(3, 2)-2*z)**2 == F(7, 4)+2*z*(1-2*z)
    # f(z)=(3/2-2z)^2/(1-z): numerator of f' is negative on [0,1/2].
    assert ((-6+8*z)*(1-z)+(F(3, 2)-2*z)**2
            == -F(3, 4)-4*(1-z)**2+1)
    # Equivalent convenient bound: -15/4+8z-4z² <= -3/4.
    assert -F(15, 4)+8*z-4*z*z == -F(3, 4)-4*(z-F(1, 2))*(z-F(3, 2))
    # Support proof: at rho=0, max(W-ell*u)=k*ell*a+k*a²/2.
    # At rho=M, W=delta*(M+u)/2. Since ell>=a/2, u>=M-ka:
    # W-ell*u <= (a-ell)M+ell*k*a-k*a²/2, identical when
    # ell=a-ka²/M. Clear M to check without symbolic rational functions.
    a, k, m = [Poly.variable(3, j) for j in range(3)]
    lm = a*m-k*a*a
    assert (a*m-lm)*m + lm*k*a-k*a*a*m/2 == lm*k*a+k*a*a*m/2


def check_triangle_optimality_and_rate():
    """Constant-cap, W-reflection symmetric triangles; no global optimum."""
    z, slope = [Poly.variable(2, j) for j in range(2)]
    # Normalize (u,W) by (M,aM), and z=ka/M. Reconstruct the three
    # upper hull vertices directly from rho=0,M and delta=+-a,s=+-k.
    left = (-z, z/2)
    middle = (1-z, 1-z/2)
    right = (1+z, 1+z/2)
    h_left = left[1]-slope*left[0]
    h_middle = middle[1]-slope*middle[0]
    h_right = right[1]-slope*right[0]
    assert h_left == z*(slope+F(1, 2))
    assert h_middle == 1-slope+z*(slope-F(1, 2))
    assert h_left-h_middle == slope-(1-z)
    assert h_middle-h_right == z*(2*slope-1)
    hull_area = ((left[1]+middle[1])*(middle[0]-left[0])
                 +(middle[1]+right[1])*(right[0]-middle[0]))
    assert hull_area == 1+4*z
    # For 1/2<=slope<=1-z, area=(A+B*slope)^2/slope,
    # A=1-z/2,B=2z. Its derivative sign is (B*slope)^2-A^2.
    a, b = 1-z/2, 2*z
    assert slope*(1+z)+h_middle == a+b*slope
    assert a-b*(1-z) == 2*(z-F(5, 8))**2+F(7, 32)
    # For slope>=1-z, derivative sign is
    # [slope*(1+2z)]^2-(z/2)^2, positive on slope>=1/2.
    assert slope*(1+z)+h_left == slope*(1+2*z)+z/2
    assert (1+2*z)/2-z/2 == (1+z)/2
    # For slope<1/2, the rightmost corner alone gives area
    # >=(1+z/2)^2/slope, exceeding the slope=1/2 value.
    assert slope*(1+z)+h_right == 1+z/2
    # Reversed symmetric triangles have area >=4*(1+z/2)*(1+2z).
    # The candidate area is <=(1+2z)^2 by the earlier exact identity.
    assert 4*(1+z/2)*(1+2*z)-(1+2*z)**2 == 3*(1+2*z)
    # Constant-cap area is aM²[1+4z+z²f(z)], so all midpoint
    # partitions have collar >=e*sum(d_i²)*g_min. The freezing
    # loss is <=3M_*²e²*sum(d_i²)/16; Cauchy sum(d_i²)>=4/N.
    endpoint = F(1, 10)
    maximum = cap(endpoint, F(1))
    assert 1-F(3, 2)*endpoint**2-F(3, 16)*maximum**2*endpoint > 0
    # Uniform grids attain 4e/N to relative error <=3e, uniformly
    # for every N>=1. These are endpoint bounds on positive coefficients.
    lower_loss = F(3, 2)*endpoint+F(3, 16)*maximum**2
    upper_loss = ((maximum-1)/endpoint
                  +(maximum+F(3, 8)*maximum**2)/2+2)
    assert lower_loss < 3 and upper_loss < 3
    # The continuum error starts at e^4: this lower coefficient follows
    # from C²>=1+2e²H and g>=1-e²D/2, with a positive lower factor.
    q = Poly.variable(1, 0)
    assert -(H(q)*D(q)).integral()/4 == -F(83, 315)


def inverse_sqrt_polynomial(x, order):
    # Taylor's integral remainder has sign (-1)^(order+1), for all x>=0.
    return sum((F((-1)**j*comb(2*j, j), 4**j)*x**j
                for j in range(order+1)), Poly.constant(x.dim, 0))


def power_sums(n, maximum):
    """Exact sum j^k, j=1,...,n; triangular binomial recurrence."""
    sums = [F(n)]
    for k in range(1, maximum+1):
        sums.append(((n+1)**(k+1)-1
                     - sum(comb(k+1, j)*sums[j] for j in range(k)))/F(k+1))
    return sums


def sum_polynomial(poly, n):
    maximum = max((k[0] for k in poly.terms), default=0)
    sums = power_sums(n, maximum)
    return sum((a*sums[k[0]] for k, a in poly.terms.items()), F(0))


def symmetric_cells(n):
    """Positive midpoints as a polynomial in j=1,...,floor(N/2)."""
    j = Poly.variable(1, 0)
    return ((2*j-(1 if n % 2 == 0 else 0))/n, n//2)


def symmetric_sum(poly, n, center_value=0):
    return 2*sum_polynomial(poly, n//2)+(center_value if n % 2 else 0)


def triangle_sum_bounds(e, n):
    """Certified bounds for the actual sharp-triangle normalized cost."""
    e, d = F(e), F(2, n)
    mn, mx = 1+F(9, 16)*e**4, cap(e, F(1))
    z_min, z_max = e*d/mx, e*d/mn
    assert 0 <= z_min <= z_max <= F(1, 2)
    f = lambda z: (F(3, 2)-2*z)**2/(1-z)
    f_lo, f_hi = f(z_max), f(z_min)
    c, _ = symmetric_cells(n)
    m = cap(e, c+F(1, n))
    lo_area = m*m+4*e*d*m+(e*d)**2*f_lo
    hi_area = m*m+4*e*d*m+(e*d)**2*f_hi
    lo = lo_area*inverse_sqrt_polynomial(e*e*D(c), 7)
    hi = hi_area*inverse_sqrt_polynomial(e*e*D(c), 6)
    if n % 2:
        cm = cap(e, F(1, n))
        cg_lo = inverse_sqrt_polynomial(e*e*D(Poly.constant(1, 0)), 7).value(0)
        cg_hi = inverse_sqrt_polynomial(e*e*D(Poly.constant(1, 0)), 6).value(0)
        center_lo = (cm*cm+4*e*d*cm+(e*d)**2*f_lo)*cg_lo
        center_hi = (cm*cm+4*e*d*cm+(e*d)**2*f_hi)*cg_hi
    else:
        center_lo = center_hi = 0
    return (d/4*symmetric_sum(lo, n, center_lo),
            d/4*symmetric_sum(hi, n, center_hi))


def source_sector_lower(e, n):
    """All source common-padding caps, same uniform midpoint partition.

    Setting p=q in b(p)+b(q)>=9e forces pointwise cap>=1+e²H+9e³/2.
    Every actual swept projection contains the zero-free-coordinate sector.
    This does not compare arbitrary different partitions or freezing tags.
    """
    e = F(e)
    q = Poly.variable(1, 0)
    radius = 1+e*e*H(q)+F(9, 2)*e**3
    primitive = (radius*radius).primitive()
    c, _ = symmetric_cells(n)
    integral = primitive.compose(c+F(1, n))-primitive.compose(c-F(1, n))
    lower = integral*inverse_sqrt_polynomial(e*e*D(c), 7)
    center = F(0)
    if n % 2:
        center = (primitive.value(F(1, n))-primitive.value(-F(1, n)))
        center *= inverse_sqrt_polynomial(e*e*D(Poly.constant(1, 0)), 7).value(0)
    return symmetric_sum(lower, n, center)/4


def rational_inverse_sqrt_bounds(value, digits=45):
    """Integer-square-root enclosure, used only for small direct cross-checks."""
    value = F(value)
    scale = 10**digits
    root = isqrt(value.numerator*scale*scale//value.denominator)
    assert root > 0
    if root*root*value.denominator == value.numerator*scale*scale:
        return F(scale, root), F(scale, root)
    return F(scale, root+1), F(scale, root)


def direct_small_sum_bounds(e, n):
    d = F(2, n)
    lower = upper = F(0)
    for j in range(n):
        left, right = -1+j*d, -1+(j+1)*d
        c = (left+right)/2
        m = cap(e, max(abs(left), abs(right)))
        slope = d/2*(1-e*d/m)
        top = m+e*d
        depth = e*d+e*d*d/(4*slope)
        coordinate_area = slope*(top+depth)**2
        gl, gu = rational_inverse_sqrt_bounds(1+e*e*D(c))
        lower += coordinate_area*gl/2
        upper += coordinate_area*gu/2
    return lower, upper


def check_continuum_and_uniform_bounds():
    q = Poly.variable(1, 0)
    assert H(q).integral() == F(8, 15)
    assert D(q).integral() == F(34, 15)
    assert (2*H(q)-D(q)/2).integral()/2 == -F(1, 30)
    coefficient4 = H(q)**2+F(9, 8)-H(q)*D(q)+F(3, 8)*D(q)**2
    assert coefficient4.integral()/2 == F(929, 630)
    # Expand cap² times the quadratic upper Taylor polynomial, in e².
    # All remaining orders >=e^6 are bounded in absolute value using
    # 0<=H<=1, 0<=D<=3, e²<=1/100. The integral /2 has length factor 1.
    # Coefficients of e^6,e^8,e^10,e^12 respectively have absolute bounds:
    remainder = (F(9, 8)+F(3, 2)*(1+F(9, 8))+F(27, 4)
                 +F(1, 100)*(F(81, 256)+F(27, 16)
                              +F(27, 8)*(1+F(9, 8)))
                 +F(1, 10000)*(F(243, 512)+F(243, 64))
                 +F(1, 1000000)*F(2187, 2048))
    # The negative e^6 contribution can instead be dropped, leaving 63/8;
    # this sharper one-sided estimate suffices for the claimed constant 8.
    one_sided = (F(9, 8)+F(27, 4)
                 +F(1, 100)*(F(81, 256)+F(27, 8)*(1+F(9, 8)))
                 +F(1, 10000)*F(243, 64)
                 +F(1, 1000000)*F(2187, 2048))
    assert remainder > 8 and one_sided < 8
    # Our independent general error: (2M e+(M+3M²/8)e²)d+2e²d².
    mx = cap(F(1, 10), F(1))
    error_coefficient = 2*mx+(mx+F(3, 8)*mx*mx)/10+F(2, 5)
    assert error_coefficient < 3   # hence error <= 3ed = 6e/N.
    # Parent's convenient bound is weaker and follows from these inequalities.
    assert mx <= 1+F(81, 80)*F(1, 100)
    assert mx+F(3, 8)*mx*mx <= 4
    # On d<=e², the refined triangles have leading finite correction 2e³.
    for endpoint, constant in [(F(1, 10), F(5, 2)), (F(1, 100), F(9, 4))]:
        maximum = cap(endpoint, F(1))
        quartic = (F(929, 1260)+6*endpoint**2
                   +maximum+F(3, 8)*maximum**2
                   +2*endpoint+F(9, 8)*endpoint**3)
        assert quartic < constant
    assert F(1, 60)-F(2, 125)-F(5, 2)*F(1, 125)**2 == F(19, 37500)


def check_uniform_source_comparison():
    q = Poly.variable(1, 0)
    c = F(9, 2)
    assert (H(q)**2-H(q)*D(q)).integral()/4 == -F(17, 90)
    assert c*(2*H(q)-D(q)).integral()/4 == -F(27, 20)
    assert c*c/2-(D(q)*H(q)**2).integral()/8 > 0
    assert -c*(D(q)*H(q)).integral()/4 == -F(83, 70)
    assert -c*c*D(q).integral()/8 == -F(459, 80)
    e = F(1, 10)
    bmax = 1+e*e+c*e**3
    remainder = (F(17, 90)+F(27, 20)*e+F(83, 70)*e**3
                 +F(459, 80)*e**4+F(3, 8)*bmax*bmax)
    assert remainder < F(3, 4)
    # source-new >= (5/2)e³-(13/4)e⁴ > 0 for 0<e<=1/10.
    assert F(5, 2)-F(13, 4)*e > 0


def angular_budget_lower_bound():
    # Exact source coverage budget, not its small-margin Taylor area estimate.
    tau = F(1, 5)
    eta = tau*(2+tau/4)/(2*(1-tau))
    assert eta == F(41, 160)
    assert 2*eta-(2+2*eta)*tau-tau*tau/4 == 0
    minimum_cap = F(1, 2)+tau*tau*eta
    assert minimum_cap == F(2041, 4000)
    # 0<=alpha<=1/2, |beta|<=1/2 => alpha²+2beta²<=3/4.
    # sqrt(1+x)<=1+x/2 and the total interval length is two.
    lower = 2*minimum_cap**2/(1+F(3, 8)*tau*tau)
    assert lower == F(4165681, 8120000) > F(1, 2)
    return lower


def check_global_source_floors():
    """Reconstruct coefficients, projection losses, and global minima."""
    q = Poly.variable(1, 0)
    # Radial endpoint pieces have Jacobian (q-c)^2/2. Their area
    # over an s-interval of length 2e is e(q-c)^2(R-2e|q-c|).
    x, displacement, rho, radius = [Poly.variable(4, j) for j in range(4)]
    # (u,Y)=(rho-s*displacement, q*u+s*displacement²/2).
    # Subtracting q times the u row leaves determinant displacement²/2.
    assert displacement**2/2*(2*x)*(radius-2*x*displacement) == (
        x*displacement**2*(radius-2*x*displacement))
    endpoint = F(1, 8)
    assert 1-F(3, 2)*endpoint**2 == F(125, 128)
    assert F(125, 128)/2-3*endpoint == F(29, 256)
    assert 1+endpoint**2+F(9, 2)*endpoint**3 == F(1049, 1024) < 2
    assert (2*H(q)-D(q)/2).integral()/4 == -F(1, 60)
    assert (H(q)*D(q)).integral() == F(332, 315) < 6
    assert -F(9, 8)*D(q).integral() == -F(51, 20)
    assert F(9, 2)-F(3, 2)*endpoint-F(51, 20)*endpoint**2 > 4
    # For e>=1/8 use only the sector and the actual finite angle budget.
    assert F(197, 200)**2*F(103, 100) < 1
    large_tilt_lower = F(197, 200)*(F(1, 2)+F(4, 15)*endpoint**2
                                   +F(9, 2)*endpoint**3)
    assert large_tilt_lower == F(1552163, 3072000) > F(1, 2)
    # Nonnegative factorizations prove the minima for every x>=0.
    x = Poly.variable(1, 0)
    minimizer = F(1, 360)
    assert 4*x**3-x*x/60+F(1, 23328000) == (
        4*(x-minimizer)**2*(x+minimizer/2))
    radial_floor = F(1, 2)-F(1, 23328000)
    # Angular secants: alpha=(1+m²-h²)/4,beta=m/2.
    midpoint, halfwidth = [Poly.variable(2, j) for j in range(2)]
    secant_a = ((1+midpoint**2-halfwidth**2)/4)**2+midpoint**2/2
    assert D(midpoint)/4-secant_a == (
        halfwidth**2*(2*(1+midpoint**2)-halfwidth**2)/16)
    angular_a, angular_d = D(q)/4, H(q)/8
    assert angular_a.integral() == F(17, 30)
    assert angular_d.integral() == F(1, 15)
    assert angular_d.integral()-angular_a.integral()/8 == -F(1, 240)
    assert F(3, 4)*angular_d.integral()/2 == F(1, 40)
    # eta>=tau/(1-tau)>=tau on the explicit budget's 0<tau<1 range.
    # The remaining cubic coefficient is >=2-3/4-1/40>1.
    assert 2-F(3, 4)-F(1, 40) > 1
    assert x**3-x*x/240+F(1, 93312000) == (
        (x-minimizer)**2*(x+minimizer/2))
    angular_floor = F(1, 2)-F(1, 93312000)
    # The published angular cubic's remaining range tau>=1/2.
    assert F(1, 2)+F(25, 4)*F(1, 2)**3 == F(41, 32)
    assert F(41, 32)**2 > F(1, 2)
    return radial_floor, angular_floor


def check_published_generic_bounds():
    """Exact constants for geometric proofs in published-generic-comparison.md."""
    e = F(1, 10)
    assert F(49, 50)**2*(1+3*e*e) < 1
    # Strip axes: nearest horizontal-edge tangent>1/3>sqrt(3)/10.
    assert F(1, 3)**2 > 3*e*e
    # Nilpotent net: Delta<=3k²/32, k<=2e, count>128/Delta.
    assert F(128)/(F(3, 32)) == F(4096, 3)
    apex_lower = F(1024, 3)/(e*e)
    assert apex_lower == F(102400, 3) > 20000
    assert F(1024, 3) > 5
    # Retention: tau/4+tau/sqrt(2)<tau; native or physically scaled
    # rational/singular domains have area>1/16.
    assert F(1, 2) < F(3, 4)**2
    assert F(1, 8)**2/2 > F(1, 16)**2
    assert F(3, 32)**2/2 > F(1, 16)**2
    assert F(1, 16*20000) > F(1, 25**4)
    grid_gain = F(26, 25)*F(49, 50)
    grid_floor = grid_gain/2
    assert grid_floor == F(637, 1250) > F(1, 2)
    cutoff = Poly.variable(1, 0)
    assert 2*grid_gain*(F(1, 4)-cutoff**2)+8*cutoff**2 == (
        grid_floor+(8-2*grid_gain)*cutoff**2)
    assert 4*grid_gain*(F(1, 8)-cutoff**2/2)+8*cutoff**2 == (
        grid_floor+(8-2*grid_gain)*cutoff**2)
    assert 8-2*grid_gain > 0 and e*e < F(1, 80)
    # Reconstruct the rational field derivative determinant. With u=r+d,
    # a=-1/16+(d²-4Y²)/(16u²), b=Y/(2u), and T=1/2-r:
    # a_Y*b_T contributes -4Y²/(16u⁴), a_T*b_Y contributes
    # (d²-4Y²)/(16u⁴). Hence det=-d²/(16u⁴).
    r, d, y = [Poly.variable(3, j) for j in range(3)]
    assert -4*y*y-(d*d-4*y*y) == -d*d
    # Clear 16(r+d)² in the bound |a|<=r/[8(r+d)].
    assert 2*r*(r+d)-(4*y*y+r*(r+2*d)) == r*r-4*y*y
    assert 64*(F(1, 64)+F(1, 2)*F(1, 16)) == 3
    assert F(4, 7) > F(3, 4)**2
    integral_floor = 2*F(1, 8)*F(3, 4)
    assert integral_floor == F(3, 16)
    small_error = (F(1, 2)-2*integral_floor)/2
    assert small_error == F(1, 16)
    assert 1+(small_error/2)/integral_floor < (1+F(1, 12))**2
    # Positive arctanh/exp series certify log(3)>13/12, exp(1)>8/3.
    assert 2*(F(1, 2)+F(1, 2)**3/3) == F(13, 12)
    assert 12*2*F(13, 12)-1 == 25
    assert 1+1+F(1, 2)+F(1, 6) == F(8, 3)
    assert F(9, 4) < 3
    assert 2*F(27, 16)**2 < 9
    assert F(27, 8)**2/2 < 9
    cell_area_upper = 3*F(13, 12)*26*F(3, 8)**25
    assert cell_area_upper == F(169, 2)*F(3, 8)**25 < F(1, 10**8)
    residual_area_upper = (small_error/2)/F(49, 50)
    assert residual_area_upper == F(25, 784)
    assert 20000*F(1, 10**8)+residual_area_upper < F(1, 4)
    assert (F(1, 4)-residual_area_upper)*10**8 > 20000000
    return apex_lower, grid_floor


def check_constructor_outputs():
    path = Path(__file__).resolve().parents[1]/'construction.py'
    spec = spec_from_file_location('constructor_under_test', path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    metric = lambda a, b: a[0]*b[0]+a[1]*b[1]+2*a[2]*b[2]
    minus = lambda a, b: tuple(x-y for x, y in zip(a, b))
    count = 0
    for e in (F(1, 100), F(1, 10)):
        for n in (1, 2, 3, 10000):
            for j in sorted({0, n//2, n-1}):
                d, c = F(2, n), -1+F(2*j+1, n)
                m = cap(e, abs(c)+1/F(n))
                slope = d/2*(1-e*d/m)
                top, depth = m+e*d, e*d+e*d*d/(4*slope)
                expected_area = slope*(top+depth)**2
                expected_lower = [(F(0), -c*depth/2, -depth/2),
                                  (F(0), (c*top-slope*(top+depth))/2, top/2),
                                  (F(0), (c*top+slope*(top+depth))/2, top/2)]
                for family in (0, 1):
                    result = module.cylinder(e, n, family*n+j)
                    axis = ((F(1), e*G(c), e*c) if family == 0
                            else (-e*G(c), F(1), e*c))
                    expected = (expected_lower if family == 0 else
                                [(p[1], -p[0], 1-p[2]) for p in expected_lower])
                    assert result['direction_scaled'] == axis
                    assert result['intercept_vertices_scaled'] == expected
                    assert result['cap_maximum'] == m
                    base = result['perpendicular_vertices_scaled']
                    for intercept, projected in zip(expected, base):
                        assert metric(projected, axis) == 0
                        difference = minus(intercept, projected)
                        assert all(difference[r]*axis[s] == difference[s]*axis[r]
                                   for r in range(3) for s in range(3))
                    ab, ac = minus(base[1], base[0]), minus(base[2], base[0])
                    gram = metric(ab, ab)*metric(ac, ac)-metric(ab, ac)**2
                    assert gram > 0
                    # A_min²=2; triangle area²=Gram/4.
                    assert gram/8 == (expected_area/4)**2/metric(axis, axis)
                    assert result['area_over_Amin'] == {
                        'numerator': expected_area/4,
                        'sqrt_denominator': 1+e*e*D(c)}
                    count += 1
    return count


def decimal_enclosure(value, places=15, upper=False):
    denominator = 10**places
    integer = value.numerator*denominator//value.denominator
    if upper and F(integer, denominator) < value:
        integer += 1
    return f'{integer//denominator}.{integer%denominator:0{places}d}'


def main():
    check_cap_identity()
    check_triangle_identities()
    check_triangle_optimality_and_rate()
    check_continuum_and_uniform_bounds()
    check_uniform_source_comparison()
    angular_lower = angular_budget_lower_bound()
    radial_floor, angular_floor = check_global_source_floors()
    apex_lower, grid_floor = check_published_generic_bounds()
    for n in range(8):
        for k, value in enumerate(power_sums(n, 16)):
            assert value == sum(j**k for j in range(1, n+1))
    for n in (1, 2, 3, 7):
        lo, hi = triangle_sum_bounds(F(1, 10), n)
        direct_lo, direct_hi = direct_small_sum_bounds(F(1, 10), n)
        assert lo <= direct_lo <= direct_hi <= hi
    checked = check_constructor_outputs()
    print('PASS: exact cap elimination and nonnegative square certificate, 0<e<=1.')
    print('PASS: refined triangle supports, exact area, and uniform finite bounds.')
    print('PASS: symmetric constant-cap triangle optimum and sharp 4e/N rate.')
    print('PASS: exact integral coefficients and one-sided e^6 remainder <=8.')
    print('PASS: uniform common-padding source comparison on d<=e^2, 0<e<=1/10.')
    print(f'PASS: {checked} independent constructor output checks (metric, vertices, area).')
    print('PASS: power-sum recurrence and independent integer-sqrt checks, odd/even N.')
    print('Angular source explicit-budget lower at tau=1/5 >= '
          +decimal_enclosure(angular_lower))
    print('Global common-padding radial floor >= '+decimal_enclosure(radial_floor))
    print('Global explicit-budget angular floor >= '+decimal_enclosure(angular_floor))
    print(f'Published nilpotent apex count > {apex_lower}; grid ratio >= {grid_floor}.')
    print('PASS: published rational product/log finite subcovers need >20 million cells.')
    cases = [(F(1, 10), 10000), (F(1, 100), 20000), (F(1, 1000), 2000000)]
    for e, n in cases:
        lo, hi = triangle_sum_bounds(e, n)
        source = source_sector_lower(e, n)
        print(f'e={e}, N={n}, cylinders={2*n}:')
        print('  exact triangle R in ['+decimal_enclosure(lo)+', '
              +decimal_enclosure(hi, upper=True)+']')
        print('  common-padding source sector lower >= '+decimal_enclosure(source))
        assert hi < source
        if e == F(1, 10):
            assert hi < F(1, 2)-F(1, 25000)
            bound = (F(1, 2)-e*e/60+F(929, 1260)*e**4+4*e**6
                     +4*e/n+8*e*e/n+F(81, 20)*e**3/n+8*e*e/n**2)
            assert hi < bound < F(1, 2)-F(1, 25000)
            assert hi < radial_floor and hi < angular_floor
            print('  general theorem bound <= '+decimal_enclosure(bound, upper=True))
    print('Scope: global floors and published-recipe comparisons have the stated hypotheses.')
    print('No global optimality, all-baseline dominance, or novelty claim is certified.')


if __name__ == '__main__':
    main()
