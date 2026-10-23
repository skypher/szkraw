"""Exact check of the edge u1-linearization coefficients e_n for every form, all n, a in [a0, amax], including the
s-free bound Q* of Q_s / C(a-1,s-1): Q* = Y'X'' + YX' - 4 u0 H - (4a/3) u1 H - ((a-3)/3) u1 (Y+Y').
Edge bound for x*y: x1 y_n + x2 y_{n-1} + y1 x_n[n>=3] + y2 x_{n-1}[n-1>=3]. Prints, per form, failing (a, n).
Usage: edge_exact.py amax"""
import sys
from fractions import Fraction as F
from math import comb as C
amax = int(sys.argv[1])
def run(a):
    R = range(a + 4)
    g = lambda d: (lambda m: d.get(m, 0))
    dd = lambda m: {n: C(m, n) for n in R}
    add = lambda *xs: {n: sum(c * x.get(n, 0) for c, x in xs) for n in R}
    A, B, D, d0, d2 = dd(a), dd(a - 1), dd(1), dd(0), dd(2)
    X = add((1, A), (-1, d0)); Xp = add((1, B), (-1, D)); Xpp = add((1, B), (-1, d0))
    Y = add((1, A), (-1, d0), (-a, D), (a, d0)); Yp = add((1, A), (a - 2, D), (-(a - 1), d2)); AmD = add((1, A), (-1, D))
    H = {n: (n - 2) * C(a, n) if n >= 3 else 0 for n in R}
    Z = lambda s: {n: (n - 2) * (C(a, s) - C(n, s)) * C(a, n) if 3 <= n <= a else 0 for n in R}
    nu = lambda s: {m: (m - 1) * (m + 1) * C(m, s - 1) * C(a, m + 1) if m + 1 >= 3 else 0 for m in R}
    J = {n: C(a - 1, n) if 2 <= n <= a - 1 else 0 for n in R}
    YY = add((1, Y), (1, Yp))
    def edge(x, y):
        out = {n: 0 for n in R}
        for n in R:
            v = x[1] * y[n] + x[2] * (y[n - 1] if n >= 1 else 0)
            if n >= 3: v += y[1] * x[n]
            if n - 1 >= 3: v += y[2] * x[n - 1]
            out[n] = v
        return out
    for seqs in (X, Xp, Xpp, Y, Yp, AmD, J):
        assert seqs[0] == 0 and all(v >= 0 for v in seqs.values())
    def E(pos, u1pos, negs):
        e = {n: F(0) for n in R}
        for c, x, y in pos:
            for n, v in edge(x, y).items(): e[n] += c * v
        for c, l in u1pos:
            for n in R: e[n] += c * l.get(n, 0)
        for c, kind, l in negs:
            for n in R:
                if kind in ('u0', 'D'): e[n] -= c * l.get(n + 1, 0)
                if kind in ('u1', 'D'): e[n] -= c * l.get(n, 0)
        return e
    K2 = [(1, Yp, Xpp), (1, Y, Xp)]
    f = {
     'K': E([(1, X, Yp), (1, Y, Xp)], [], [(4, 'D', H)]),
     'L': E([(a - 2, AmD, X), (a, AmD, Xp)], [], [(4, 'D', H)]),
     'R': E([(a, AmD, Xp)], [], [(8, 'D', H)]),
     'R2': E([(a - 2, AmD, Xpp)], [], [(4 * a, 'D', H)]),
     "K''": E(K2, [], [(4, 'D', H)]),
     'Ka': E([(a - 1, x, y) for _, x, y in K2], [], [(4 * a, 'D', H)]),
     'Q*': E(K2, [], [(4, 'u0', H), (F(4 * a, 3), 'u1', H), (F(a - 3, 3), 'u1', YY)]),
     'Psi': E([(a, AmD, J)], [], [(F((a - 1) * (a - 2), 2), 'u1', YY)]),
     'Qhat': E([(a - 1, x, y) for _, x, y in K2], [(2, nu(1)), (2, nu(2))], [(4 * a, 'u0', H), (4, 'u1', Z(1)), (4, 'u1', Z(2))]),
    }
    return {name: [n for n, v in e.items() if v < 0] for name, e in f.items()}
fails = {}
for a in range(3, amax + 1):
    for name, bad in run(a).items():
        if bad: fails.setdefault(name, []).append((a, bad[:5]))
for name in ['K', 'L', 'R', 'R2', "K''", 'Ka', 'Q*', 'Psi', 'Qhat']:
    print(f'{name}: fails at {fails.get(name, [])[:8]}')
