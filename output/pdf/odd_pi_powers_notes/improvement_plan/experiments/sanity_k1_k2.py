"""Float sanity checks for section 4.4 of the plan (not certificates).

k=1 : mu(pi)   <= m(D+G)/D                      (x=i, Theta=pi/2)
k=2 : mu(pi^2) <= (floor(m/2))(D'+G')/D'        (x=-1, Theta=pi, free parity elimination)
k=3 : balanced-minima elimination heuristic
      E = (m(1+r)/k)(D+G)/(D-rG), r=(k-1)/(m+2-k)    (HEURISTIC ONLY)
"""
import math
import numpy as np
from scipy.optimize import brentq
from fast_eval import gamma


def rates_theta(L, offsets, nu, theta, g):
    nu = np.asarray(nu, float)
    c = np.array([1 - 2 * t / L for t in offsets])
    M = nu.sum(); m = M - 1
    Y = brentq(lambda Y: 2 * np.sum(nu * np.arctan(c / (2 * Y))) - theta,
               1e-6, 4 * M + 10, xtol=1e-14)
    Fc = c / 2 * np.log((1 + (2 * Y / c) ** 2) / 4) + 2 * Y * np.arctan(c / (2 * Y))
    D0 = np.sum(nu * Fc) - theta * Y - m
    G0 = m + np.sum(nu * c) * math.log(2)
    return m, D0 + g, G0 - g


def balanced(M, theta):
    m = M - 1
    D0 = -M * math.log(2 * math.sin(theta / (2 * M))) - m
    return m, D0, m + M * math.log(2)


print("k=1 balanced (x=i):")
best = min((m * (D + G) / D, M) for M in range(2, 40)
           for m, D, G in [balanced(M, math.pi / 2)] if D > 0)
print("  min_M m(D+G)/D = %.4f at M=%d" % best)

print("k=2 balanced (x=-1, Theta=pi):")
best = min(((m // 2) * (D + G) / D, M) for M in range(2, 60)
           for m, D, G in [balanced(M, math.pi)] if D > 0)
print("  min_M floor(m/2)(D+G)/D = %.4f at M=%d" % best)

print("k=2 two-level nested (x=-1), L=39, t=0..T:")
res = []
for T in (4, 8, 11):
    offs = tuple(range(T + 1))
    for a in range(2, 40, 2):
        for b in range(1, 8):
            nu = [a] + [b] * T
            g = gamma(39, offs, nu)
            m, D, G = rates_theta(39, offs, nu, math.pi, g)
            if D > 0 and G >= 0:
                res.append(((m // 2) * (D + G) / D, a, b, T, m))
res.sort()
print("  best: E=%.4f a=%d b=%d T=%d m=%d" % res[0])

print("k=3 balanced-minima elimination HEURISTIC (x=i):")
for M in (8, 10, 12, 15, 20, 30):
    m, D, G = balanced(M, math.pi / 2)
    k = 3; r = (k - 1) / (m + 2 - k)
    if D - r * G > 0:
        print("  M=%d: E_bal=%.3f" % (M, (m * (1 + r) / k) * (D + G) / (D - r * G)))
m, D, G = 186, 651.2972962706768, 255.5962938344585
r = 2 / (m - 1)
print("  twelve-layer: E_bal=%.3f  (resultant: %.3f)" %
      ((m * (1 + r) / 3) * (D + G) / (D - r * G), m * (D + G) / (D - 2 * G)))
