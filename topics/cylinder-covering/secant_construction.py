#!/usr/bin/env python3
"""Exact compact generator for compatible secants with a quartic overlap cap.

Coordinates are (x, y, z/sqrt(2)), with metric diag(1,1,2). Every output
coefficient is rational for rational epsilon. Only the requested cylinder is
constructed, even when n is large. See SECANT-THEOREM.md for the proof.
"""

import argparse
from fractions import Fraction as F
import json


def cap(e, q):
    return 1 + e*e*(q*q+q**4)/2 + F(9, 16)*e**4


def padding(e, d):
    """Uniform cap addition; d is the angular cell width."""
    m = cap(e, F(1))
    k0 = m*(e+e*e/2) + 2*e*e
    return d*(k0+m*e*e*d/4)/(2*(1-e))


def dot(a, b):
    return a[0]*b[0] + a[1]*b[1] + 2*a[2]*b[2]


def project(p, v):
    ratio = dot(p, v)/dot(v, v)
    return tuple(x-ratio*y for x, y in zip(p, v))


def cylinder(e, n, index):
    """Return one of exactly 2*n cylinders, with 0<e<=1/10 and n>=1."""
    e = F(e)
    if not 0 < e <= F(1, 10):
        raise ValueError('epsilon must be in (0, 1/10]')
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError('n must be a positive integer')
    if not isinstance(index, int) or isinstance(index, bool) or not 0 <= index < 2*n:
        raise ValueError('index must lie in [0, 2*n)')
    family, j = divmod(index, n)
    d = F(2, n)
    left = -1+j*d
    right = left+d
    center = (left+right)/2
    horizontal = (1+left*right)/2
    m = cap(e, max(abs(left), abs(right)))
    delta = padding(e, d)
    cutoff = (m+delta)/2
    lower = [(F(0), F(0), F(0)),
             (F(0), left*cutoff, cutoff),
             (F(0), right*cutoff, cutoff)]
    if family == 0:
        intercepts = lower
        direction = (F(1), e*horizontal, e*center)
    else:
        intercepts = [(p[1], -p[0], 1-p[2]) for p in lower]
        direction = (-e*horizontal, F(1), e*center)
    return {
        'index': index,
        'family': 'lower' if family == 0 else 'upper',
        'interval': (left, right),
        'midpoint': center,
        'secant_coefficient': horizontal,
        'continuous_cap_maximum': m,
        'discrete_padding': delta,
        'physical_radial_cutoff': cutoff,
        'direction_scaled': direction,
        'intercept_vertices_scaled': intercepts,
        'perpendicular_vertices_scaled': [project(p, direction) for p in intercepts],
        'area_over_Amin': {
            'numerator': d*cutoff*cutoff/2,
            'sqrt_denominator': dot(direction, direction),
        },
    }


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--epsilon', default='1/10', type=F)
    parser.add_argument('--n', default=10000, type=int)
    parser.add_argument('--index', default=0, type=int)
    args = parser.parse_args()
    result = cylinder(args.epsilon, args.n, args.index)
    result['cover'] = {
        'epsilon': args.epsilon,
        'physical_tau': 2*args.epsilon,
        'cylinder_count': 2*args.n,
        'maximum_axis_tangent_squared': 3*args.epsilon**2*(1-F(1, args.n))**2,
        'coordinate_convention': '(x, y, z/sqrt(2)); metric diag(1,1,2)',
        'body': '0<=s<=1, |x|<=1-s, |y|<=s, z=sqrt(2)*s',
        'Amin': 'sqrt(2)',
    }
    print(json.dumps(result, default=encode, indent=2))


if __name__ == '__main__':
    main()
