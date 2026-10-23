"""Cubic weighted B-detour as a quadratic form in the profile's u = f(l) (exact, symbolic in the ratio).
D(l,n) = K phi2(l) phi_n(l+1) - L c_{l+1} phi_{n+2}(l) only involves products u_a u_{n+d}, a in {0,1,2}.
For each weight w = a + n + d, Abel tails from the most balanced pair: T2 = q_2, T1 = q_1 + q_2, T0 = q_0 + q_1 + q_2.
Each tail is a quadratic form in (r, t, tau, sigma). Test: after the trade r sigma <= t tau, every tail is copositive
by the coefficient criterion (all coefficients but r tau >= 0, r tau >= -2 sqrt(rr tautau)).
Usage: cubic_quadB_abel.py lmax nmax"""
import sys, math, itertools
from fractions import Fraction as Fr
import sympy as sp
lmax, nmax = int(sys.argv[1]), int(sys.argv[2])
r, t, tau, sig = sp.symbols('r t tau sigma', nonnegative=True)
RHO = lambda x: r + t * x + tau * sp.binomial(x, 2) + sig * sp.binomial(x, 3)
def Drho(j, x):
    return [RHO(x), t + tau * x + sig * sp.binomial(x, 2), tau + sig * x, sig][j] if j <= 3 else 0
def form(l, n):
    U = {}  # coefficient of u_a * u_b keyed by (a, b) with a = small index
    K, L = (n + 1) * (n + 2), 8 * (n - 1)
    phi2 = {2: Drho(0, l + 2), 1: 2 * Drho(1, l + 1), 0: Drho(2, l)}
    phin1 = {}
    for i in range(0, 4):
        if i > n: continue
        cfi = sp.binomial(n, i) * Drho(i, l + 1 + n - i)
        for e in (n - i, n - i + 1):
            phin1[e] = phin1.get(e, 0) + cfi
    c1 = {0: Drho(0, l + 1), 1: Drho(0, l + 1)}
    phin2 = {}
    for j in range(0, 4):
        if j > n + 2: continue
        phin2[n + 2 - j] = phin2.get(n + 2 - j, 0) + sp.binomial(n + 2, j) * Drho(j, l + n + 2 - j)
    for a, x in phi2.items():
        for b, y in phin1.items():
            U[(a, b)] = U.get((a, b), 0) + K * x * y
    for a, x in c1.items():
        for b, y in phin2.items():
            U[(a, b)] = U.get((a, b), 0) - L * x * y
    return U
def coef(expr):
    P = sp.Poly(sp.expand(expr), r, t, tau, sig)
    g = {}
    for m, v in zip(P.monoms(), P.coeffs()):
        g[m] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    return g
mon = {'rr': (2, 0, 0, 0), 'rt': (1, 1, 0, 0), 'rtau': (1, 0, 1, 0), 'rs': (1, 0, 0, 1), 'tt': (0, 2, 0, 0),
       'ttau': (0, 1, 1, 0), 'ts': (0, 1, 0, 1), 'tautau': (0, 0, 2, 0), 'taus': (0, 0, 1, 1), 'ss': (0, 0, 0, 2)}
def copos_ok(g):
    gg = {k: g.get(v, Fr(0)) for k, v in mon.items()}
    gg['ttau'] += min(gg['rs'], 0); gg['rs'] = max(gg['rs'], 0)
    for k, v in gg.items():
        if k != 'rtau' and v < 0: return False, k
    if gg['rtau'] < 0 and gg['rtau'] ** 2 > 4 * gg['rr'] * gg['tautau']: return False, 'rtau'
    return True, None
fails = []; cnt = 0
for l in range(0, lmax + 1):
    for n in range(3, nmax + 1):
        U = form(l, n)
        weights = {}
        for (a, b), v in U.items(): weights.setdefault(a + b, {})[a] = weights.get(a + b, {}).get(a, 0) + v
        for w, row in weights.items():
            # tails from the most balanced small index
            acc = 0
            for a in sorted(row, reverse=True):
                if 2 * a > w: continue
                acc = acc + row[a]; cnt += 1
                ok, why = copos_ok(coef(acc))
                if not ok: fails.append((l, n, w, a, why))
rel = [f for f in fails if not (f[0] == 0 and f[3] == 0)]
print(f'relevant failures (excluding l = 0, a = 0, where u_0 = d_0 = 0): {len(rel)} {rel[:10]}')
print(f'{cnt} tail forms for l <= {lmax}, 3 <= n <= {nmax}: failures {len(fails)} {fails[:10]}')
