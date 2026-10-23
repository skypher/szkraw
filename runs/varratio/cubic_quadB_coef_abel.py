"""Cubic weighted B-detour, decomposition D = D(r,0,tau) + rest (Theorem 8.11 gives D(r,0,tau) >= 0).
The rest is >= 0 under r sigma <= t tau if the single coefficients satisfy
  k_rt >= 0, k_tt >= 0, k_ts >= 0 (off the corner), k_taus >= 0, k_ss >= 0, k_ttau + min(k_rs, 0) >= 0.
Each is a scalar quadratic form in u = f(l) (pairs (a, n+d), a <= 2). Test each by Abel tails in u, bounding negative
u_0 u_w terms by theta u_1 u_{w-1} + (1-theta) l u_1 u_w (theta from a grid, per weight by search).
Usage: cubic_quadB_coef_abel.py lmax nmax"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cubic_quadB_abel.py')).read()
exec(src.split('fails = []; cnt = 0')[0].replace('lmax, nmax = int(sys.argv[1]), int(sys.argv[2])', ''))
lmax, nmax = int(sys.argv[1]), int(sys.argv[2])
targets = {'rt': ['rt'], 'tt': ['tt'], 'ts': ['ts'], 'taus': ['taus'], 'ss': ['ss'], 'ttau': ['ttau'], 'ttau+rs': ['ttau', 'rs']}
grid = [Fr(k, 8) for k in range(9)]
def scalar(expr, keys):
    g = coef(expr)
    vals = [g.get(mon[k], Fr(0)) for k in keys]
    return vals
def row_value(vals, keys):
    if keys == ['ttau', 'rs']: return vals[0] + vals[1]
    return vals[0]
def passes(rows, l):
    ws = sorted(rows)
    def tails_ok(w, q1w):
        row = rows.get(w, {}); acc = 0
        if 2 in row and 4 <= w:
            acc += row[2]
            if acc < 0: return False
        if 2 <= w:
            acc += q1w
            if acc < 0: return False
        return True
    def rec(idx, carry):
        if idx == len(ws): return carry >= 0 or tails_ok(ws[-1] + 1, carry)
        w = ws[idx]; row = rows[w]
        base = row.get(1, 0) + carry; neg = min(row.get(0, 0), 0)
        nxt = idx + 1 < len(ws) and ws[idx + 1] == w + 1
        for th in grid:
            if not tails_ok(w, base + th * neg): continue
            newc = (1 - th) * l * neg
            if not nxt and idx + 1 < len(ws) and newc < 0:
                if not tails_ok(w + 1, newc): continue
                newc = 0
            if rec(idx + 1, newc): return True
            if neg == 0: break
        return False
    return rec(0, 0)
fails = {k: [] for k in targets}; cnt = 0
for l in range(0, lmax + 1):
    for n in range(2, nmax + 1):
        if (l, n) == (0, 2): continue
        U = form(l, n)
        for name, keys in targets.items():
            if name == 'ts' and (l, n) == (0, 2): continue
            rows = {}
            for (a, b), v in U.items():
                vals = scalar(v, keys)
                if keys == ['ttau', 'rs']:
                    pass
                rows.setdefault(a + b, {})
                rows[a + b].setdefault(a, [0] * len(keys))
                rows[a + b][a] = [x + y for x, y in zip(rows[a + b][a], vals)]
            # the trade min(k_rs,0) applies to the whole coefficient form, not entrywise: test the combined form
            # conservatively entrywise: ttau entry + min(rs entry, 0) per pair
            rows2 = {w: {a: row_value(v, keys) for a, v in row.items()} for w, row in rows.items()}
            cnt += 1
            if not passes(rows2, l): fails[name].append((l, n))
print(f'{cnt} (coefficient, l, n) tests, l <= {lmax}, n <= {nmax}:')
for k, v in fails.items(): print(f'  {k}: failures {len(v)} {v[:12]}')
