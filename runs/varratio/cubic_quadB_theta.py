"""Cubic weighted B-detour in u = f(l): negative u_0 u_w terms bounded by
u_0 u_w <= theta u_1 u_{w-1} + (1 - theta) l u_1 u_w   (log-concavity and convexity, both valid).
For each (l, n) report which theta in a grid make all Abel tails (a = 2, then a = 1) copositive after the trade
r sigma <= t tau. Usage: cubic_quadB_theta.py lmax nmax"""
import sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cubic_quadB_abel.py')).read()
exec(src.split('fails = []; cnt = 0')[0].replace('lmax, nmax = int(sys.argv[1]), int(sys.argv[2])', ''))
lmax, nmax = int(sys.argv[1]), int(sys.argv[2])
def to_vec(expr):
    g = coef(expr); return {k: g.get(v, Fr(0)) for k, v in mon.items()}
def ok_vec(gg):
    gg = dict(gg); gg['ttau'] += min(gg['rs'], 0); gg['rs'] = max(gg['rs'], 0)
    for k, v in gg.items():
        if k != 'rtau' and v < 0: return False
    return not (gg['rtau'] < 0 and gg['rtau'] ** 2 > 4 * gg['rr'] * gg['tautau'])
add = lambda a, b, c=1: {k: a.get(k, 0) + c * b.get(k, 0) for k in mon}
Z = {k: Fr(0) for k in mon}
def passes(rows, l, th):
    q1 = {w: dict(row.get(1, Z)) for w, row in rows.items()}
    for w, row in rows.items():
        q0 = row.get(0, Z)
        neg = {k: min(v, 0) for k, v in q0.items()}
        q1[w] = add(q1[w], neg, th)
        if any(v < 0 for v in neg.values()):
            if w + 1 not in q1: q1[w + 1] = dict(Z)
            q1[w + 1] = add(q1[w + 1], neg, (1 - th) * l)
    for w in set(rows) | set(q1):
        row = rows.get(w, {})
        acc = dict(Z)
        if 2 in row and 4 <= w:
            acc = add(acc, row[2])
            if not ok_vec(acc): return False
        if 2 <= w:
            acc = add(acc, q1.get(w, Z))
            if not ok_vec(acc): return False
    return True
thetas = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)]
nopass = []; summary = {}
for l in range(0, lmax + 1):
    for n in range(4, nmax + 1):
        U = form(l, n); rows = {}
        for (a, b), v in U.items():
            rows.setdefault(a + b, {}); rows[a + b][a] = add(rows[a + b].get(a, Z), to_vec(v))
        good = [th for th in thetas if passes(rows, l, th)]
        summary[(l, n)] = good
        if not good: nopass.append((l, n))
print('(l,n) with no passing theta:', nopass[:20], 'total', len(nopass), 'of', len(summary))
from collections import Counter
print('theta usage (smallest passing):', Counter(str(min(g)) for g in summary.values() if g))

# per-weight theta by depth-first search with pruning
grid = [Fr(k, 8) for k in range(9)]
def passes_dfs(rows, l):
    ws = sorted(rows)
    wmax = ws[-1] + 1
    negs = {w: {k: min(v, 0) for k, v in rows[w].get(0, Z).items()} for w in ws}
    def tails_ok(w, q1w):
        row = rows.get(w, {})
        acc = dict(Z)
        if 2 in row and 4 <= w:
            acc = add(acc, row[2])
            if not ok_vec(acc): return False
        if 2 <= w:
            acc = add(acc, q1w)
            if not ok_vec(acc): return False
        return True
    def rec(idx, carry):
        if idx == len(ws):
            w = wmax
            return tails_ok(w, carry) if any(v != 0 for v in carry.values()) else True
        w = ws[idx]
        base = add(rows[w].get(1, Z), carry)
        nxt_gap = (idx + 1 < len(ws) and ws[idx + 1] == w + 1) or idx + 1 == len(ws)
        for th in grid:
            q1w = add(base, negs[w], th)
            if not tails_ok(w, q1w): continue
            newcarry = {k: (1 - th) * l * v for k, v in negs[w].items()}
            if not nxt_gap and any(v < 0 for v in newcarry.values()):
                if not tails_ok(w + 1, newcarry): continue
                newcarry = dict(Z)
            if rec(idx + 1, newcarry): return True
        return False
    return rec(0, dict(Z))
still = []
for (l, n) in nopass:
    U = form(l, n); rows = {}
    for (a, b), v in U.items():
        rows.setdefault(a + b, {}); rows[a + b][a] = add(rows[a + b].get(a, Z), to_vec(v))
    if not passes_dfs(rows, l): still.append((l, n))
print('after per-weight theta search (grid 1/8):', 'still failing', still[:20], 'total', len(still), 'of', len(nopass))
