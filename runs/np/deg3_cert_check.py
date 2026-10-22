"""Exact check of the piecewise degree-3 certificate: lam22 = max(0, lam13 - [x1x3]), mu13 = max(0, [x1x3] - lam13),
all multipliers >= 0 and the identity exact, at random rational (nu, k) with nu2^2 >= nu1 nu3 (boundary included).
Usage: deg3_cert_check.py samples seed"""
import sys, random
from fractions import Fraction as F
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/np')
from deg3_cert import lam, Q, x, n1, n2, n3, k
c = lambda i, j: Q.coeff_monomial(x[i] * x[j])
S, rng = int(sys.argv[1]), random.Random(int(sys.argv[2])); bad = 0; neg22 = 0
for _ in range(S):
    a1 = F(rng.randint(1, 50), rng.randint(1, 10)); a2 = F(rng.randint(0, 50), rng.randint(1, 10))
    a3 = a2 * a2 / a1 * rng.choice([F(0), F(1), F(rng.randint(0, 100), 100)])
    kk = rng.choice([2, 3, 3, 4, 5, 6, 8, 12, 30])
    sub = {n1: a1, n2: a2, n3: a3, k: kk}
    L = {key: sp.Rational(v.subs(sub)) for key, v in lam.items() if key != (2, 2)}
    f22 = sp.Rational((lam[(1, 3)] - c(1, 3)).subs(sub))
    L[(2, 2)] = max(f22, 0); neg22 += int(bool(f22 < 0))
    M = {(1, 1): c(1, 1) - lam[(1, 1)], (1, 2): c(1, 2) - lam[(1, 2)], (2, 3): c(2, 3) - lam[(2, 3)], (3, 3): c(3, 3) - lam[(3, 3)]}
    M = {key: sp.Rational(v.subs(sub)) for key, v in M.items()}
    M[(1, 3)] = max(-f22, 0); M[(2, 2)] = sp.Rational(c(2, 2).subs(sub)) - L[(2, 2)]
    D = lambda i, j: x[i] * x[j] - x[i - 1] * x[j + 1]
    recon = sum(v * D(*key) for key, v in L.items()) + sum(v * x[a] * x[b] for (a, b), v in M.items())
    ok = sp.expand(recon - Q.as_expr().subs(sub)) == 0 and all(v >= 0 for v in list(L.values()) + list(M.values()))
    if not ok:
        bad += 1; print('FAIL', sub)
print(f'{bad}/{S} failures; forced lam22 negative (case 2 used) in {neg22} samples')
