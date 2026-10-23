"""Exact witnesses that the full key needs the ratio's log-concavity: P = (p0, p1, tau, 0, ...) with nonnegative but
non-log-concave Newton coefficients (p1^2 < p0 tau), monotone b and b >= 0 in the window, ratio <= 1, and key < 0.
Far-field geometric u (u0 = 1/w). Exact rational arithmetic. Usage: key_nolc_witness.py a w"""
import sys, math
import sympy as sp
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_cert_lp import key_poly
a = int(sys.argv[1]); w = sp.Rational(sys.argv[2])
u = [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]
key, P, b = key_poly(u, a); Pv = P[:a + 1]
best = None
for p0 in [sp.Rational(1, 10 ** e) for e in range(0, 7)]:
    for tau in [sp.Rational(1, 10 ** e) for e in range(2, 14)]:
        for p1 in [sp.Integer(0), tau * sp.Rational(1, 10), tau]:
            sub = {Pv[0]: p0, Pv[1]: p1, Pv[2]: tau}
            sub.update({Pv[k]: 0 for k in range(3, a + 1)})
            if p1 ** 2 >= p0 * tau: continue  # want NOT log-concave
            rho_top = p0 + p1 * a + tau * math.comb(a, 2)
            if rho_top > 1: continue
            if any((b(m + 1) - b(m)).subs(sub) < 0 for m in range(a)) or any(b(m).subs(sub) < 0 for m in range(a + 1)): continue
            v = key.subs(sub)
            if best is None or v < best[0]: best = (v, p0, p1, tau)
print(f'a={a} w={w}: most negative key over the grid = {float(best[0]):.4g} at p0={best[1]}, p1={best[2]}, tau={best[3]}' if best else 'no feasible point')
if best and best[0] < 0: print('  EXACT WITNESS: key < 0 with nonnegative non-log-concave Newton coefficients and monotone b in the window')
