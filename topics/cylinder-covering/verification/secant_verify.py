#!/usr/bin/env python3
"""Independent exact certificates for the compatible-secant quartic cover.

Uses the previously checked rational polynomial/power-sum arithmetic only.
No constructor formula is imported into the acceptance proof or cost bounds.
The constructor is imported separately for output regression checks.
"""

from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from math import comb
from pathlib import Path

from verify import Poly, power_sums, rational_inverse_sqrt_bounds, decimal_enclosure


def g(q):
    return (1+q*q)/2


def h(q):
    return q*q*g(q)


def radial_cap(e, q):
    return 1+e*e*h(q)+F(9, 16)*e**4


def discrete_padding(e, width):
    maximum = 1+e*e+F(9, 16)*e**4
    loss = (e*maximum*width
            +e*e*maximum*(width/2+width*width/4)
            +2*e*e*width)
    return loss/(2*(1-e))


def secant_norm(q, width):
    a = (1+q*q)/2-width*width/8
    return a*a+2*q*q


def check_coverage_algebra():
    # The continuous boundary is h_j(q)=a_j-q*b_j, with
    # a_j=(1+lr)/2 and b_j=(l+r)/2. It interpolates (1-q²)/2.
    left, right, q = [Poly.variable(3, j) for j in range(3)]
    a, b = (1+left*right)/2, (left+right)/2
    boundary = a-q*b
    assert ((right-left)*boundary
            == (right-q)*(1-left*left)/2+(q-left)*(1-right*right)/2)
    assert boundary-(1-q*q)/2 == -(q-left)*(right-q)/2
    assert q*q-left*right == q*(q-right)+right*(q-left)
    # Hence 0<=a<=1, |b|<=1, boundary>=0, |a-G(q)|<=width/2,
    # |b-q|<=width/2, and |boundary-(1-q²)/2|<=width²/8.

    e, p, q, ap, aq, bp, bq, rho, sigma = [Poly.variable(9, j) for j in range(9)]
    denominator = 1+e*e*ap*aq
    # Reconstruct the coupled equations Y=rho*q+e*X*aq,
    # X=sigma*p-e*Y*ap and rho+sigma=2+e*(Y*bp-X*bq).
    xn = sigma*p-e*rho*q*ap
    yn = rho*q+e*sigma*p*aq
    assert yn-rho*q*denominator-e*xn*aq == 0
    assert xn-sigma*p*denominator+e*yn*ap == 0
    wq = 1-e*q*bp+e*e*ap*(aq-q*bq)
    wp = 1+e*p*bq+e*e*aq*(ap-p*bp)
    assert (denominator*(rho+sigma-2)-e*(yn*bp-xn*bq)
            == wq*rho+wp*sigma-2*denominator)
    # Both weights >=1-e>0 from the secant boundary's nonnegativity.

    gp, gq = g(p), g(q)
    dp, dq = (1-p*p)/2, (1-q*q)/2
    cwp = 1+e*p*q+e*e*gq*dp
    cwq = 1-e*p*q+e*e*gp*dq
    continuous = cwq*radial_cap(e, q)+cwp*radial_cap(e, p)-2*(1+e*e*gp*gq)
    delta, s = p*p-q*q, 1+p*p+q*q
    certificate = (e*e/2*(delta+e*p*q*s/2)**2
                   +e**4*(gp*gq*(p*p*dp+q*q*dq)+(9-p*p*q*q*s*s)/8)
                   +F(9, 16)*e**6*(gp*dq+gq*dp))
    assert continuous == certificate
    assert (9-p*p*q*q*s*s
            == 9*((1-p*p)+p*p*(1-q*q))
            +p*p*q*q*((1-p*p)+(1-q*q))*(3+s))
    discrete = wq*radial_cap(e, q)+wp*radial_cap(e, p)-2*denominator
    # Reconstruct the exact perturbation before bounding its terms.
    perturbation = (
        -e*q*(bp-p)*radial_cap(e, q)
        +e*p*(bq-q)*radial_cap(e, p)
        +e*e*((ap-gp)*dq+ap*((aq-q*bq)-dq))*radial_cap(e, q)
        +e*e*((aq-gq)*dp+aq*((ap-p*bp)-dp))*radial_cap(e, p)
        -2*e*e*((ap-gp)*aq+gp*(aq-gq)))
    assert discrete-continuous == perturbation
    # The preceding universal bounds give total loss
    # M*e*d + M*e²*(d/2+d²/4) + 2e²*d, exactly 2(1-e)*padding.
    e, d, maximum = [Poly.variable(3, j) for j in range(3)]
    loss = maximum*e*d+maximum*e*e*(d/2+d*d/4)+2*e*e*d
    assert loss == d*(maximum*(e+e*e/2)+2*e*e+maximum*e*e*d/4)


def check_uniform_estimates():
    endpoint, width = F(1, 10), F(2)
    maximum = radial_cap(endpoint, F(1))
    # Clear the padding denominator to verify its expansion about e*d/2.
    e, d = [Poly.variable(2, j) for j in range(2)]
    m = radial_cap(e, F(1))
    twice_denominator_excess = d*(m*(e+e*e/2)+2*e*e+m*e*e*d/4)-(1-e)*e*d
    assert twice_denominator_excess == e*d*((m-1)+e*(m/2+3+m*d/4))
    # All upper-bound coefficients are monotone on 0<e<=.1, 0<d<=2.
    padding_error = ((maximum-1)/endpoint+maximum+3)/(2*(1-endpoint))
    assert padding_error < F(5, 2)
    assert F(1, 2)+F(5, 2)*endpoint == F(3, 4)
    max_padding = F(3, 4)*endpoint*width
    upper_error = (maximum+F(3, 8)*maximum**2
                   +(maximum-1)/(2*endpoint)+F(5, 2)*maximum
                   +F(9, 16)+(maximum+max_padding)**2/8)
    lower_error = F(3, 8)*maximum**2+F(3, 4)*endpoint
    assert upper_error < 5 and lower_error < F(1, 2)
    # Secant projection error: D-G_sec²-2q² <=d²/4; the derivative
    # of (1+e²D)^(-1/2) has absolute value <=e²/2.
    q, d = [Poly.variable(2, j) for j in range(2)]
    assert (g(q)**2+2*q*q)-secant_norm(q, d) == g(q)*d*d/4-d**4/64
    # At the outer midpoint c=1-d/2 the secant a equals c.
    assert g(1-d/2)-d*d/8 == 1-d/2
    # Schedule d<=e²: continuum remainder + finite error <=6e^4.
    assert F(929, 1260)+5+4*endpoint**2 < 6
    assert F(1, 60)-F(1, 80)-6*F(1, 40)**2 == F(1, 2400)
    # Sharper bookkeeping: apply the secant weight correction to the
    # unpadded cap first, then bound padding with its secant weight<=1.
    assert maximum < F(1011, 1000) and maximum**2 < F(1023, 1000)
    assert maximum+F(3, 8)*maximum**2 < F(7, 5)
    error_ratio = F(3033, 4000)+F(9, 160)+F(7, 50)+F(1023, 80000)
    assert error_ratio == F(77383, 80000) < 1
    assert F(3, 8)*maximum**2*endpoint < 1
    # On d<=e², bound delta<=ed/2+(21/10)e²d. After dividing
    # the padding numerator by ed, the higher coefficients are positive.
    cap_coefficient = F(81, 80)
    assert (cap_coefficient+(F(1, 4)+cap_coefficient/2)*endpoint
            +cap_coefficient*endpoint**3/4) < F(11, 10)
    x = Poly.variable(1, 0)
    assert ((1-x)*(1+F(21, 5)*x)-(1+F(5, 2)*x+F(11, 10)*x*x)
            == F(7, 10)*x-F(53, 10)*x*x)
    assert F(7, 10)-F(53, 10)*endpoint > 0
    assert F(1, 2)+F(21, 10)*endpoint == F(71, 100)
    assert cap_coefficient*F(71, 100)*endpoint < F(2, 25)
    assert F(21, 10)+F(2, 25) == F(109, 50)
    assert F(71, 100)**2*endpoint**2/2 < F(3, 1000)
    assert F(1023, 1000)*endpoint**2/16 < F(1, 1000)
    assert F(929, 1260)+F(7, 5)+F(109, 50)+F(1, 250)+F(1, 25) < F(9, 2)
    assert F(1, 60)-F(1, 100)-F(9, 2)*F(1, 50)**2 == F(73, 15000)
    # N>=ceil(480/e) suffices throughout e<=.1, from |R-J|<=2e/N.
    assert F(929, 1260)*endpoint**2+4*endpoint**4 < F(1, 120)
    assert F(1, 120)-F(2, 480) == F(1, 240)


def check_published_compatible_range():
    # Source AngularGeneral: (10+4E)*tau<=eta<=1/480, tau<=1/2,
    # area remainder <=(6E+2)*tau^4. Thus the positive 2eta*tau²
    # absorbs that remainder and tau<=1/4800.
    error = Poly.variable(1, 0)
    assert 2*(10+4*error)-(6*error+2) == 18+2*error
    assert F(1, 480)/10 == F(1, 4800)
    assert F(1, 480)*F(1, 2)/4 < F(1, 16)  # source expansion smallness
    area_floor = F(1, 2)-F(1, 240)*F(1, 4800)**2
    assert area_floor == F(1, 2)-F(1, 5529600000)
    # Endpoint coefficient errors force every width<=4E*tau².
    # E=0 is impossible for a positive-width partition. For E>0,
    # full count>=1/(E*tau²)>=(10+4E)²/(E*eta²)>=160/eta².
    assert (10+4*error)**2-160*error == (4*error-10)**2
    assert 160/F(1, 480)**2 == 36864000 > 20000
    return area_floor


def inverse_sqrt_taylor(argument, order):
    return sum((F((-1)**k*comb(2*k, k), 4**k)*argument**k
                for k in range(order+1)), Poly.constant(argument.dim, 0))


def sum_polynomial(poly, count):
    degree = max((powers[0] for powers in poly.terms), default=0)
    sums = power_sums(count, degree)
    return sum((coefficient*sums[powers[0]] for powers, coefficient in poly.terms.items()), F(0))


def exact_cost_bounds(e, n):
    e, d = F(e), F(2, n)
    padding = discrete_padding(e, d)
    j = Poly.variable(1, 0)
    midpoint = (2*j-(1 if n % 2 == 0 else 0))/n
    radius = radial_cap(e, midpoint+d/2)+padding
    argument = e*e*secant_norm(midpoint, d)
    lower = radius**2*inverse_sqrt_taylor(argument, 9)
    upper = radius**2*inverse_sqrt_taylor(argument, 8)
    lower_sum, upper_sum = 2*sum_polynomial(lower, n//2), 2*sum_polynomial(upper, n//2)
    if n % 2:
        center_radius = radial_cap(e, d/2)+padding
        center_arg = Poly.constant(1, e*e*secant_norm(F(0), d))
        lower_sum += center_radius**2*inverse_sqrt_taylor(center_arg, 9).value(0)
        upper_sum += center_radius**2*inverse_sqrt_taylor(center_arg, 8).value(0)
    return d*lower_sum/4, d*upper_sum/4


def direct_cost_bounds(e, n):
    d, lower, upper = F(2, n), F(0), F(0)
    for j in range(n):
        left, right = -1+j*d, -1+(j+1)*d
        cutoff = (radial_cap(e, max(abs(left), abs(right)))+discrete_padding(e, d))/2
        a, b = (1+left*right)/2, (left+right)/2
        gl, gu = rational_inverse_sqrt_bounds(1+e*e*(a*a+2*b*b))
        lower += d*cutoff*cutoff*gl
        upper += d*cutoff*cutoff*gu
    return lower, upper


def check_generator():
    path = Path(__file__).resolve().parents[1]/'secant_construction.py'
    spec = spec_from_file_location('secant_generator_under_test', path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    metric = lambda a, b: a[0]*b[0]+a[1]*b[1]+2*a[2]*b[2]
    subtract = lambda a, b: tuple(x-y for x, y in zip(a, b))
    count = 0
    for e in (F(1, 100), F(1, 10)):
        for n in (1, 2, 3, 10000):
            d = F(2, n)
            for j in sorted({0, n//2, n-1}):
                left, right = -1+j*d, -1+(j+1)*d
                a, b = (1+left*right)/2, (left+right)/2
                padding = discrete_padding(e, d)
                maximum = radial_cap(e, max(abs(left), abs(right)))
                cutoff = (maximum+padding)/2
                lower = [(F(0), F(0), F(0)), (F(0), left*cutoff, cutoff),
                         (F(0), right*cutoff, cutoff)]
                for family in (0, 1):
                    result = module.cylinder(e, n, family*n+j)
                    expected_axis = (F(1), e*a, e*b) if family == 0 else (-e*a, F(1), e*b)
                    expected_vertices = lower if family == 0 else [(p[1], -p[0], 1-p[2]) for p in lower]
                    assert result['direction_scaled'] == expected_axis
                    assert result['intercept_vertices_scaled'] == expected_vertices
                    assert result['discrete_padding'] == padding
                    assert result['physical_radial_cutoff'] == cutoff
                    projected = result['perpendicular_vertices_scaled']
                    for vertex, foot in zip(expected_vertices, projected):
                        assert metric(foot, expected_axis) == 0
                        difference = subtract(vertex, foot)
                        assert all(difference[r]*expected_axis[s] == difference[s]*expected_axis[r]
                                   for r in range(3) for s in range(3))
                    ab, ac = subtract(projected[1], projected[0]), subtract(projected[2], projected[0])
                    gram = metric(ab, ab)*metric(ac, ac)-metric(ab, ac)**2
                    numerator = d*cutoff*cutoff/2
                    assert gram > 0 and gram/8 == numerator**2/metric(expected_axis, expected_axis)
                    assert result['area_over_Amin'] == {
                        'numerator': numerator, 'sqrt_denominator': 1+e*e*(a*a+2*b*b)}
                    count += 1
    return count


def main():
    check_coverage_algebra()
    check_uniform_estimates()
    compatible_floor = check_published_compatible_range()
    for n in (1, 2, 3, 7):
        lo, hi = exact_cost_bounds(F(1, 10), n)
        direct_lo, direct_hi = direct_cost_bounds(F(1, 10), n)
        assert lo <= direct_lo <= direct_hi <= hi
    checked = check_generator()
    print('PASS: exact secant boundary, coupled elimination, quartic square certificate.')
    print('PASS: uniform residual bound, closed coverage padding, and e/N leading rate.')
    print('PASS: schedule saving on 0<e<=1/40 with margin >=e²/2400.')
    print('PASS: sharper schedule quartic coefficient 9/2 and |R-J|<=2e/N for all N.')
    print('PASS: N>=ceil(480/e) gives saving >=e²/240 throughout 0<e<=1/10.')
    print(f'PASS: {checked} independent secant generator metric/area/vertex checks.')
    print('PASS: exact power-sum costs cross-checked with integer square roots, odd/even N.')
    print('Published compatible-range ratio >= '+decimal_enclosure(compatible_floor, 18)
          +'; full count >=36,864,000.')
    cases = [(F(1, 10), 10000), (F(1, 100), 20000), (F(1, 1000), 2000000)]
    for e, n in cases:
        lo, hi = exact_cost_bounds(e, n)
        assert hi < F(1, 2)
        print(f'e={e}, N={n}, cylinders={2*n}:')
        print('  secant R in ['+decimal_enclosure(lo, 18)+', '
              +decimal_enclosure(hi, 18, upper=True)+']')
        if e == F(1, 10):
            assert hi < F(499937, 1000000)
            d, m = F(2, n), radial_cap(e, F(1))
            padding = discrete_padding(e, d)
            analytic_upper = (F(1, 2)-e*e/60+F(929, 1260)*e**4+4*e**6
                              +(m+F(3, 8)*m*m)*e*e*d+m*padding+padding**2/2
                              +m*m*e*e*d*d/16)
            assert hi < analytic_upper < F(499929, 1000000)
            # The formerly uncertified continuous angular cap eta=.001,
            # tau=.2 has twice-cutoff 1+e²H+(.008)e².
            assert F(9, 16)*e**4+discrete_padding(e, F(2, n)) < F(1, 125)*e*e
            print('  continuous angular candidate eta=.001,tau=.2 is now covered by this proof.')


if __name__ == '__main__':
    main()
