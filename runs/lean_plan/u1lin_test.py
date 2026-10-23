"""Lean planning test: 'u1-linearization' of the key forms of Theorem 8.16 (equivalent to Lemma 8.15's weight sums).
For u0-free nonnegative linear forms: (sum a_i u_i)(sum b_j u_j) >= u_1 * sum_m (sum_{i+j=m+1} a_i b_j) u_m (u_i u_j >= u_1 u_{i+j-1}).
Negative terms: c*u0*lin <= c*u1*shift(lin) (u_0 u_n <= u_1 u_{n-1}), c*u1*lin as is, c*D*lin = both.
Positive u1*lin terms (u1 nu_s) count directly. Then form >= u_1 sum_m e_m u_m; reports the a for which some e_m < 0,
and checks that every factor coefficient is >= 0 and u0-free. Usage: u1lin_test.py amax"""
import sys
from math import comb as C
from fractions import Fraction as F
amax = int(sys.argv[1])
def forms(a):
    R = range(a + 3)
    dd = lambda m: {n: C(m, n) for n in R}
    add = lambda *xs: {n: sum(c * x.get(n, 0) for c, x in xs) for n in R}
    A, B, D, d0, d2 = dd(a), dd(a - 1), dd(1), dd(0), dd(2)
    X = add((1, A), (-1, d0)); Xp = add((1, B), (-1, D)); Xpp = add((1, B), (-1, d0))
    Y = add((1, A), (-1, d0), (-a, D), (a, d0)); Yp = add((1, A), (a - 2, D), (-(a - 1), d2)); AmD = add((1, A), (-1, D))
    H = {n: (n - 2) * C(a, n) if n >= 3 else 0 for n in R}
    Z = lambda s: {n: (n - 2) * (C(a, s) - C(n, s)) * C(a, n) if 3 <= n <= a else 0 for n in R}
    nu = lambda s: {n: ((n + 1 - 2) * (n + 1) * C(n, s - 1) * C(a, n + 1) if n + 1 >= 3 else 0) for n in R}
    J = {n: C(a - 1, n) if 2 <= n <= a - 1 else 0 for n in R}
    YY = add((1, Y), (1, Yp))
    cpp = C(a - 1, 2)
    out = {}
    # (positive products [(c, lin1, lin2)], positive u1-terms [(c, lin)], negatives [(c, kind, lin)])
    out['L'] = ([(1, AmD, add((a - 2, X), (a, Xp)))], [], [(4, 'D', H)])
    out['R'] = ([(a, AmD, Xp)], [], [(8, 'D', H)])
    out['R2'] = ([(a - 2, AmD, Xpp)], [], [(4 * a, 'D', H)])
    K = [(1, Yp, Xpp), (1, Y, Xp)]
    out["K''"] = (K, [], [(4, 'D', H)])
    out['Ka'] = ([(a - 1, x, y) for _, x, y in K], [], [(4 * a, 'D', H)])
    for s in range(3, a + 1):
        cp, cs = C(a - 1, s - 1), C(a - 1, s)
        out[f'Q{s}'] = ([(cp, x, y) for _, x, y in K], [(2, nu(s))], [(4 * cp, 'u0', H), (4, 'u1', Z(s)), (cs, 'u1', YY)])
    out['Psi'] = ([(a, AmD, J)], [], [(cpp, 'u1', YY)])
    out['Qhat'] = ([(a - 1, x, y) for _, x, y in K], [(2, nu(1)), (2, nu(2))], [(4 * a, 'u0', H), (4, 'u1', Z(1)), (4, 'u1', Z(2))])
    return out, R
def run(a):
    res = {}
    fs, R = forms(a)
    for name, (prods, posu1, negs) in fs.items():
        e = {m: F(0) for m in range(2 * a + 4)}
        ok_sign = True
        for c, x, y in prods:
            for i in R:
                for j in R:
                    if x[i] * y[j] == 0: continue
                    if i == 0 or j == 0 or x[i] < 0 or y[j] < 0: ok_sign = False
                    e[i + j - 1] += c * x[i] * y[j]
        for c, l in posu1:
            for n, v in l.items(): e[n] += c * v
        for c, kind, l in negs:
            for n, v in l.items():
                if v == 0: continue
                if kind in ('u0', 'D'): e[n - 1] -= c * v          # u0 u_n <= u1 u_{n-1}
                if kind in ('u1', 'D'): e[n] -= c * v
        bad = [m for m, v in e.items() if v < 0]
        res[name] = (ok_sign, bad)
    return res
fails = {}; signs = set()
for a in range(3, amax + 1):
    for name, (ok, bad) in run(a).items():
        if not ok: signs.add(name)
        if bad: fails.setdefault(name if not name.startswith('Q') or name == 'Qhat' else 'Q_s', set()).add(a)
print('factor sign/u0-free violations:', signs or 'none')
for k in ['L', 'R', 'R2', "K''", 'Ka', 'Q_s', 'Psi', 'Qhat']:
    print(f'{k}: e_m < 0 for a in {sorted(fails.get(k, []))[:15]}')
