"""Cubic weighted B-detour: Abel tails plus the convexity bound u_0 <= l u_1 (u_0 = d_l, d_0 = 0).
Per weight w: rows q_2, q_1, q_0 (quadratic forms in the ratio). Negative ratio-monomials of q_0 are bounded with
u_0 u_w <= l u_1 u_w and moved to the pair (1, w) of weight w+1; then tails T2 = q_2 and T1 = q_1 + q_2 must be
copositive (trade r sigma <= t tau, r tau via sqrt(rr tautau)). Usage: cubic_quadB_abel2.py lmax nmax"""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import sympy as sp
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'cubic_quadB_abel.py')).read().split('fails = []; cnt = 0')[0].replace('lmax, nmax = int(sys.argv[1]), int(sys.argv[2])', ''))
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
fails = []; cnt = 0
for l in range(0, lmax + 1):
    for n in range(3, nmax + 1):
        U = form(l, n)
        rows = {}
        for (a, b), v in U.items():
            rows.setdefault(a + b, {}); rows[a + b][a] = add(rows[a + b].get(a, {}), to_vec(v))
        carry = {}
        for w in sorted(rows):
            row = rows[w]
            if w in carry: row[1] = add(row.get(1, {}), carry[w])
            q0 = row.get(0, {k: Fr(0) for k in mon})
            neg = {k: min(v, 0) for k, v in q0.items()}
            if any(v < 0 for v in neg.values()):
                carry[w + 1] = add(carry.get(w + 1, {k: Fr(0) for k in mon}), neg, l)
            acc = {k: Fr(0) for k in mon}
            for a in (2, 1):
                if a in row and 2 * a <= w:
                    acc = add(acc, row[a]); cnt += 1
                    ok, why = ok_vec(acc)
                    if not ok: fails.append((l, n, w, a, why))
            # weight w+1 may not exist as a row: then the carry must be absorbed by a fresh (1, w) entry
        for w, cv in carry.items():
            if w not in rows and any(v < 0 for v in cv.values()): fails.append((l, n, w, 'carry-unabsorbed'))
print(f'{cnt} tails, l <= {lmax}, 3 <= n <= {nmax}: failures {len(fails)} {fails[:10]}')
