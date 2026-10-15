#!/usr/bin/env python3
"""Compact exact generator for the quartic-cap triangular cylinder cover.

Coordinates returned are (x, y, z/sqrt(2)); the metric is diag(1,1,2).
Every coefficient is rational for rational epsilon. No list of N cylinders
is allocated. See THEOREM.md for the geometric proof, and the independent
verification/verify.py for the certificate.
"""

import argparse
from fractions import Fraction as F
import json


def G(q):
    return (1 + q*q) / 2


def cap(e, q):
    return 1 + e*e*q*q*G(q) + F(9, 16)*e**4


def dot(a, b):
    return a[0]*b[0] + a[1]*b[1] + 2*a[2]*b[2]


def project(p, v):
    ratio = dot(p, v) / dot(v, v)
    return tuple(x - ratio*y for x, y in zip(p, v))


def cylinder(e, n, index):
    """Return one cylinder, indexed 0,...,2*n-1, using exact fractions.

    The first n are lower-family cylinders; the remaining n are upper-family.
    The permitted range is 0 < e <= 1/10, n >= 1.
    """
    e = F(e)
    if not 0 < e <= F(1, 10):
        raise ValueError('epsilon must be in (0, 1/10]')
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError('n must be a positive integer')
    if not isinstance(index, int) or isinstance(index, bool) or not 0 <= index < 2*n:
        raise ValueError('index must lie in [0, 2*n)')
    family, j = divmod(index, n)
    d = F(2, n)
    left = -1 + j*d
    right = left + d
    c = (left + right)/2
    M = cap(e, max(abs(left), abs(right)))
    t = e*d/M
    ell = d/2*(1-t)
    U = M+e*d
    V = e*d + e*d*d/(4*ell)
    height = U+V
    # The affine variables are u and W, with y=(c*u+W)/2, z/H=u/2.
    uv = [(-V, F(0)), (U, -ell*height), (U, ell*height)]
    lower = [(F(0), (c*u+w)/2, u/2) for u, w in uv]
    if family == 0:
        intercepts = lower
        direction = (F(1), e*G(c), e*c)
    else:
        intercepts = [(p[1], -p[0], 1-p[2]) for p in lower]
        direction = (-e*G(c), F(1), e*c)
    bases = [project(p, direction) for p in intercepts]
    coordinate_area = ell*height*height
    return {
        'index': index,
        'family': 'lower' if family == 0 else 'upper',
        'interval': (left, right),
        'midpoint': c,
        'cap_maximum': M,
        'triangle': {'ell': ell, 'U': U, 'V': V},
        'direction_scaled': direction,
        'intercept_vertices_scaled': intercepts,
        'perpendicular_vertices_scaled': bases,
        'area_over_Amin': {
            'numerator': coordinate_area/4,
            'sqrt_denominator': dot(direction, direction),
        },
    }


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--epsilon', default='1/10', type=F)
    p.add_argument('--n', default=10000, type=int)
    p.add_argument('--index', default=0, type=int)
    args = p.parse_args()
    result = cylinder(args.epsilon, args.n, args.index)
    result['cover'] = {
        'epsilon': args.epsilon, 'physical_tau': 2*args.epsilon,
        'cylinder_count': 2*args.n,
        'coordinate_convention': '(x, y, z/sqrt(2)); metric diag(1,1,2)',
        'body': '0<=s<=1, |x|<=1-s, |y|<=s, z=sqrt(2)*s',
        'Amin': 'sqrt(2)',
        'unit_axis': 'direction_scaled interpreted physically, divided by its Euclidean norm',
    }
    print(json.dumps(result, default=encode, indent=2))


if __name__ == '__main__':
    main()
