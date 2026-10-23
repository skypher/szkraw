"""Lean planning test: does the 'D-linearization' prove each key form of Theorem 8.16 nonnegative?
Each form = sum of (linear form) x (pair form) - (negative terms of type D*lin, u0*lin, u1*lin).
Pair form: sum_j g_j (u_j + u_{j+1}); u_i (u_j + u_{j+1}) >= D u_{i+j} for i, j >= 1 (Lemma 8.3); the term j = 0 gives
D*u_i exactly; terms with i = 0 are dropped. Negative u0*lin and u1*lin are bounded by D*lin. Then the form is
>= D * sum_n (p_n - q_n) u_n, and it suffices that p_n >= q_n for all n. Exact over a = 3..amax.
Usage: dlin_test.py amax"""
import sys
from fractions import Fraction as F
from math import comb as C
amax = int(sys.argv[1])
def lin_dd(a, lam):  # linear form sum_m lam[m] d_{l+m} -> coefficients of u_n
    return {n: sum(l * C(m, n) for m, l in lam.items()) for n in range(a + 2)}
def pair_dd(a, lam):  # same form as pair form: d_{l+m} = sum_n C(m-1,n)(u_n+u_{n+1}) for m >= 1
    assert all(m >= 1 for m in lam)
    return {n: sum(l * C(m - 1, n) for m, l in lam.items()) for n in range(a + 2)}
def forms(a):
    A = {a: 1}; B = {a - 1: 1}; D = {1: 1}; d0 = {0: 1}; d2 = {2: 1}
    add = lambda *xs: {m: sum(x.get(m, 0) * c for c, x in xs) for m in set().union(*[x for _, x in xs])}
    X = add((1, A), (-1, d0)); Xp = add((1, B), (-1, D)); Xpp = add((1, B), (-1, d0))
    Y = add((1, A), (-1, d0), (-a, add((1, D), (-1, d0))))           # B0(l,a) = A - u0 - a u1
    Yp = add((1, A), (a - 2, D), (-(a - 1), d2))                       # B0(l+1,a-1)
    AmD = add((1, A), (-1, D))
    yn = lambda n: C(a, n)
    H = {n: (n - 2) * yn(n) if n >= 3 else 0 for n in range(a + 2)}
    def Z(s): return {n: (n - 2) * (C(a, s) - C(n, s)) * yn(n) if 3 <= n <= a else 0 for n in range(a + 2)}
    def nu(s): return {n - 1: (n - 2) * n * C(n - 1, s - 1) * yn(n) for n in range(3, a + 1)}
    J = {n: C(a - 1, n) if 2 <= n <= a - 1 else 0 for n in range(a + 2)}
    cpp = C(a - 1, 2)
    lin = lambda lam: lin_dd(a, lam)
    out = {}
    # each entry: list of (coef, linear-coeffs dict, pair-coeffs dict) products, list of (coef, kind, lin dict) negatives
    out['L'] = ([(1, {n: (a - 2) * lin(X)[n] + a * lin(Xp)[n] for n in range(a + 2)}, pair_dd(a, AmD))], [(4, 'D', H)])
    out['R'] = ([(a, lin(Xp), pair_dd(a, AmD))], [(8, 'D', H)])
    out['R2'] = ([(a - 2, lin(Xpp), pair_dd(a, AmD))], [(4 * a, 'D', H)])
    Kpp_pos = [(1, lin(Xpp), pair_dd(a, Yp)), (1, lin(Y), pair_dd(a, Xp))]
    out["K''"] = (Kpp_pos, [(4, 'D', H)])
    out['Ka'] = ([(a - 1, l, p) for _, l, p in Kpp_pos], [(4 * (a - 1) + 4, 'D', H)])
    for s in range(3, a + 1):
        cp, cs = C(a - 1, s - 1), C(a - 1, s)
        YY = {n: lin(Y)[n] + lin(Yp)[n] for n in range(a + 2)}
        out[f'Q{s}'] = ([(cp, l, p) for _, l, p in Kpp_pos], [(4 * cp, 'u0', H), (4, 'u1', Z(s)), (cs, 'u1', YY)])
    YY = {n: lin(Y)[n] + lin(Yp)[n] for n in range(a + 2)}
    out['Psi'] = ([(a, J, pair_dd(a, AmD))], [(cpp, 'u1', YY)])
    Z12 = {n: Z(1)[n] + Z(2)[n] for n in range(a + 2)}
    out['Qhat'] = ([(a - 1, l, p) for _, l, p in Kpp_pos], [(4 * a, 'u0', H), (4, 'u1', Z12)])
    return out
def check(a):
    res = {}
    for name, (pos, neg) in forms(a).items():
        p = {n: F(0) for n in range(2 * a + 3)}
        for c, l, g in pos:
            for i, li in l.items():
                for j, gj in g.items():
                    if li == 0 or gj == 0: continue
                    if j == 0: p[i] += c * li * gj            # g_0 u_i (u_0+u_1) = g_0 D u_i
                    elif i >= 1:
                        assert li >= 0 and gj >= 0 or (li * gj >= 0), (name, i, j)
                        p[i + j] += c * li * gj
        q = {n: F(0) for n in range(2 * a + 3)}
        for c, kind, l in neg:
            for n, v in l.items(): q[n] += c * v
        bad = [n for n in p if p[n] < q[n]]
        res[name] = bad
    return res
fails = {}
for a in range(3, amax + 1):
    for name, bad in check(a).items():
        if bad: fails.setdefault(name, []).append((a, bad[:6]))
for name in ['L', 'R', 'R2', "K''", 'Ka', 'Psi', 'Qhat'] + [f'Q{s}' for s in range(3, 6)]:
    f = fails.get(name, [])
    print(f'{name}: failing a = {[x[0] for x in f][:20]}', ('e.g. ' + str(f[0])) if f else '')
qs = sorted({k for k in fails if k.startswith('Q') and k != 'Qhat'})
print('Q_s failures (any s):', {k: [x[0] for x in fails[k]][:8] for k in qs})
