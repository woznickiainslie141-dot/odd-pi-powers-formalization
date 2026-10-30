"""Small exact checks of the Pade normalization and the audit examples.

These finite checks supplement, rather than replace, the general proofs.
Requires sympy. No numerical approximation is used for the identities.
"""

from fractions import Fraction as F
from math import comb, factorial, lcm, prod
from pathlib import Path
import json
import sympy as s


def mul(a, b, length):
    out = [F(0)]*length
    for i, x in enumerate(a):
        for j, y in enumerate(b[:length-i]):
            out[i+j] += x*y
    return out


def matrix_at_i(m, n):
    dn = lcm(*range(1, n+1))
    pref = factorial(m)*dn**m*factorial(n)**(m+1)
    A = [[s.S.Zero for _ in range(m+1)] for _ in range(m+1)]
    for h in range(m+1):
        for ell in range(n+1):
            series = [F(comb(h, j)*(-ell)**(h-j))
                      if j <= h else F(0) for j in range(m+1)]
            for r in range(n+1):
                if r == ell:
                    continue
                gap = r-ell
                factor = [F((-1)**j*comb(m+j, j), gap**(m+1+j))
                          for j in range(m+1)]
                series = mul(series, factor, m+1)
            for k in range(m+1):
                val = F(pref, factorial(k))*series[m-k]
                assert val.denominator == 1
                A[h][k] += int(val)*s.I**(n-ell)
    c = s.Rational(
        (-1)**(m*(m+1)//2)*pref**(m+1),
        factorial(n)**((m+1)**2)*prod(factorial(k) for k in range(m+1)),
    )
    det = s.expand(s.Matrix(A).det())
    expected = s.expand(c*(s.I-1)**(n*(m+1)))
    assert s.simplify(det-expected) == 0 and det != 0
    return {'m': m, 'n': n, 'integrality': True, 'determinant': True}


def audit_examples():
    z, Y, t = s.symbols('z Y t')
    # Attachment's prefactor, already for h=0,m=1,n=2.
    wrong_pref = s.Rational(1, 2)
    coeff = s.residue(z/(z*(z+1)*(z+2))**2, z, 0)*wrong_pref
    # This is the coefficient of x^2 log x in the incorrectly normalized row.
    assert coeff == s.Rational(1, 8)
    # A nonzero value at one root need not give a nonzero three-root product
    # when the binomial splits over Q(i).
    U = 4*Y**2+2*s.I*Y-1
    assert s.expand(U.subs(Y, s.I/2)) == -3
    assert s.resultant(Y**3+s.I/8, U, Y) == 0
    # Proposed a1=a2=a3=N=1 kernel: mirror symmetry fails.
    R = 8*(t-1)**3/(t+s.Rational(1,2))**3
    assert R.subs(t,1) == 0 and R.subs(t,-3) == s.Rational(4096,125)
    # Correct parity of the proper unweighted q=4 kernel.
    symmetry = []
    for n in range(1,7):
        r = factorial(n)*s.rf(t+1,n)*s.rf(t+2*n+1,n)/s.rf(t+n+s.Rational(1,2),n+1)**3
        assert s.cancel(r.subs(t,-t-3*n-1)-(-1)**(n+1)*r) == 0
        symmetry.append(n)
    return {
        'wrong_normalization_log_coefficient': str(coeff),
        'split_norm_counterexample_U_at_i_over_2': '-3',
        'split_norm_counterexample_resultant': '0',
        'proposed_kernel_R_minus_3': '4096/125',
        'proper_kernel_symmetry_checked_n': symmetry,
    }


if __name__ == '__main__':
    cases = [(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)]
    result = {'pade_checks': [matrix_at_i(m,n) for m,n in cases],
              'audit_examples': audit_examples(), 'passed': True}
    dest = Path(__file__).resolve().parents[1] / 'data' / 'identity_checks.json'
    dest.parent.mkdir(exist_ok=True)
    dest.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n',
                    encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))
