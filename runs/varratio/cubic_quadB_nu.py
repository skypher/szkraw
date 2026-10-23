"""Cubic weighted B-detour as a quadratic form in the base profile's Newton sequence nu (nu_0 = 0),
u_k = f_k(l) = sum_h C(l,h) nu_{k+h}. Abel tails per weight W over pairs (i, W-i), 1 <= i <= W/2, from the centre;
each tail is a quadratic form in (r,t,tau,sigma), tested copositive after the trade r sigma <= t tau
(coefficients but r tau >= 0, r tau >= -2 sqrt(rr tautau)). Usage: cubic_quadB_nu.py lmax nmax"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import math
import sympy as sp
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cubic_quadB_abel.py')).read()
exec(src.split('fails = []; cnt = 0')[0].replace('lmax, nmax = int(sys.argv[1]), int(sys.argv[2])', ''))
lmax, nmax = int(sys.argv[1]), int(sys.argv[2])
def to_vec(expr):
    g = coef(expr); return {k: g.get(v, Fr(0)) for k, v in mon.items()}
def ok_vec(gg):
    gg = dict(gg); gg['ttau'] += min(gg['rs'], 0); gg['rs'] = max(gg['rs'], 0)
    for k, v in gg.items():
        if k != 'rtau' and v < 0: return False, k
    if gg['rtau'] < 0 and gg['rtau'] ** 2 > 4 * gg['rr'] * gg['tautau']: return False, 'rtau'
    return True, None
add = lambda a, b, c=1: {k: a.get(k, 0) + c * b.get(k, 0) for k in mon}
fails = []; cnt = 0; inner = []; maxneg = [0]
for l in range(0, lmax + 1):
    for n in range(2, nmax + 1):
        if (l, n) == (0, 2): continue
        U = form(l, n)
        V = {}
        for (a, b), v in U.items():
            vec = to_vec(v)
            for h in range(l + 1):
                for h2 in range(l + 1):
                    i, j = a + h, b + h2
                    if i == 0 or j == 0: continue  # nu_0 = 0
                    key = (min(i, j), max(i, j))
                    V[key] = add(V.get(key, {k: Fr(0) for k in mon}), vec, math.comb(l, h) * math.comb(l, h2))
        rows = {}
        for (i, j), vec in V.items(): rows.setdefault(i + j, {})[i] = vec
        for W, row in rows.items():
            acc = {k: Fr(0) for k in mon}
            for i in sorted(row, reverse=True):
                acc = add(acc, row[i]); cnt += 1
                ok, why = ok_vec(acc)
                if not ok: fails.append((l, n, W, i, why))
                if i >= 2:
                    ok2, why2 = ok_vec(row[i])
                    if not ok2: inner.append((l, n, W, i, why2))
                ok3, _ = ok_vec(row[i])
                if not ok3: maxneg[0] = max(maxneg[0], i)
print(f'{cnt} tails in nu, l <= {lmax}, 2 <= n <= {nmax} except (0,2): failures {len(fails)} {fails[:12]}')
print(f'pairs (i, W-i) with i >= 2 not copositive on their own: {len(inner)} {inner[:8]}')
print('largest index i with a non-copositive single pair (i, W-i):', maxneg[0])
