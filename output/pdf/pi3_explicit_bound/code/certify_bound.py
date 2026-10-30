"""Exact rational certificate for the explicit pi-cubed exponent.

Only the Python standard library is used. The certificate evaluates the
closed formula; the analytical argument is in main.tex.
"""

from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


PLACES = 40
SCALE = 10**PLACES


def outward(lo, hi):
    """Enclose rational endpoints by rationals of denominator 10**40."""
    a = (lo.numerator * SCALE) // lo.denominator
    b = -((-hi.numerator * SCALE) // hi.denominator)
    return F(a, SCALE), F(b, SCALE)


def atan_bounds(x, terms=40):
    s = sum(((-1)**k * x**(2*k+1) / (2*k+1)
             for k in range(terms)), F(0))
    t = (-1)**terms * x**(2*terms+1) / (2*terms+1)
    return min(s, s+t), max(s, s+t)


def sin_bounds(x, terms=10):
    assert 0 < x < F(1, 10)
    s = sum(((-1)**k * x**(2*k+1) / factorial(2*k+1)
             for k in range(terms)), F(0))
    t = (-1)**terms * x**(2*terms+1) / factorial(2*terms+1)
    return min(s, s+t), max(s, s+t)


def log_bounds(x, terms=50):
    """Positive atanh series for 1 <= x <= 2, with a rational tail."""
    assert 1 <= x <= 2
    y = (x-1)/(x+1)
    s = 2 * sum((y**(2*k+1)/(2*k+1)
                 for k in range(terms)), F(0))
    tail = 2*y**(2*terms+1)/((2*terms+1)*(1-y*y))
    return s, s+tail


def endpoint_string(x):
    assert (x*SCALE).denominator == 1
    v = int(x*SCALE)
    sign = '-' if v < 0 else ''
    v = abs(v)
    return f'{sign}{v//SCALE}.{v%SCALE:0{PLACES}d}'


def display_interval(lo, hi):
    a, b = outward(lo, hi)
    return [endpoint_string(a), endpoint_string(b)]


def certify(m):
    # Machin's identity: pi = 16 atan(1/5) - 4 atan(1/239).
    a0, a1 = atan_bounds(F(1, 5))
    b0, b1 = atan_bounds(F(1, 239))
    pi0, pi1 = outward(16*a0-4*b1, 16*a1-4*b0)
    M = m+1
    x0, x1 = pi0/(4*M), pi1/(4*M)
    # sin is increasing on this interval, contained in (0,1/10).
    s0 = sin_bounds(x0)[0]
    s1 = sin_bounds(x1)[1]
    t0, t1 = outward(2*s0, 2*s1)
    # Scale the logarithm argument into [1,2].
    shift = 0
    while t0*2**shift < 1:
        shift += 1
    assert t1*2**shift <= 2
    l20, l21 = outward(*log_bounds(F(2)))
    u0 = log_bounds(t0*2**shift)[0]
    u1 = log_bounds(t1*2**shift)[1]
    logt0, logt1 = outward(u0-shift*l21, u1-shift*l20)
    D0, D1 = outward(-M*logt1-m, -M*logt0-m)
    G0, G1 = outward(m+M*l20, m+M*l21)
    gap0, gap1 = D0-2*G1, D1-2*G0
    assert gap0 > 0
    # E=m(D+G)/(D-2G): decreasing in D and increasing in G.
    E0 = m*(D1+G0)/(D1-2*G0)
    E1 = m*(D0+G1)/(D0-2*G1)
    target = F('2028.145383')
    assert E1 < target
    return {
        'method': 'exact fractions; Machin; alternating sine; atanh logarithm',
        'm': m,
        'pi_interval': display_interval(pi0, pi1),
        'D_interval': display_interval(D0, D1),
        'G_interval': display_interval(G0, G1),
        'gap_interval': display_interval(gap0, gap1),
        'E_interval': display_interval(E0, E1),
        'certified_E_less_than': str(target),
        'decimal_target': '2028.145383',
        'passed': True,
    }


if __name__ == '__main__':
    result = certify(289)
    dest = Path(__file__).resolve().parents[1] / 'data' / 'bound_certificate.json'
    dest.parent.mkdir(exist_ok=True)
    dest.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n',
                    encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))
