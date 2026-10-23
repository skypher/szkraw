"""Degree-2 certificate search for the full key inequality of (G) at fixed numeric log-concave u (u_n = f_n(l)).
Key(P) = A0(l,a) B0(l+1,a-1) + B0(l,a) A0(l+1,a-2) - c_{l+1} (4 H1 - 2 V1), quadratic in P = (P_0..P_a), P_k = D^k rho(l).
Generators (nonnegative on the feasible set): g_m * P_k with g_m = b_{l+m+1} - b_{l+m} (monotone b in the window),
bb_m * P_k with bb_m = b_{l+m} (b >= 0), P_k, P_k P_j, and LC differences P_i P_j - P_{i-1} P_{j+1} (1 <= i <= j).
Usage: key_cert_lp.py amax trials seed [nolc]"""
import sys, random, math
import sympy as sp
import numpy as np
from scipy.optimize import linprog
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3])); nolc = 'nolc' in sys.argv

def key_poly(u, a):
    P = sp.symbols('P0:%d' % (a + 2))
    rho = lambda n: sum(math.comb(n, k) * P[k] for k in range(n + 1))
    d = lambda n: sum(math.comb(n, m) * u[m] for m in range(n + 1))
    c = lambda n: rho(n) * d(n); b = lambda n: d(n) - c(n)
    fdif = lambda n, l: sum((-1) ** (n - i) * math.comb(n, i) * d(l + i) for i in range(n + 1))
    A0 = lambda l, aa: b(l + aa) - b(l)
    B0 = lambda l, aa: c(l + aa) - c(l) - aa * (c(l + 1) - c(l))
    H1 = sum((n - 2) * math.comb(a, n) * (1 - rho(n)) * u[n] for n in range(3, a + 1))
    Drho = lambda x: rho(x + 1) - rho(x)
    V1 = sum((n - 2) * math.comb(a, n) * n * Drho(n - 1) * u[n - 1] for n in range(3, a + 1))
    key = A0(0, a) * B0(1, a - 1) + B0(0, a) * A0(1, a - 2) - c(1) * (4 * H1 - 2 * V1)
    return sp.expand(key), P, b

def lc_u(rng, L):
    ratios = sorted((sp.Rational(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [sp.Rational(rng.randint(0, 30), 10)]
    if u[0] == 0: u = [sp.Integer(0), sp.Integer(1)]
    else: u.append(u[0] * ratios[0])
    for r in ratios[1:]: u.append(u[-1] * r)
    return u

if __name__ == '__main__':
    cases = []
    for _ in range(T):
        a = rng.randint(3, amax); cases.append((a, lc_u(rng, a + 3), 'rand'))
    if '--adv' in sys.argv:
        cases = []
        alist = [int(z) for z in sys.argv[sys.argv.index('--adv') + 1].split(',')] if len(sys.argv) > sys.argv.index('--adv') + 1 and sys.argv[sys.argv.index('--adv') + 1][0].isdigit() else range(3, amax + 1)
        for a in alist:
            for w in [sp.Rational(1, 10), sp.Rational(1, 100), sp.Rational(1, 1000)]:
                cases.append((a, [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)], f'geo w={w}'))
    for a, u, kind in cases:
        key, P, b = key_poly(u, a)
        Pv = P[:a + 1]
        gens = []
        for m in range(0, a):
            g = sp.expand(b(m + 1) - b(m))
            for k in range(a + 1): gens.append(sp.expand(g * Pv[k]))
        for m in range(0, a + 1):
            for k in range(a + 1): gens.append(sp.expand(b(m) * Pv[k]))
        for k in range(a + 1): gens.append(Pv[k])
        for i in range(a + 1):
            for j in range(i, a + 1): gens.append(Pv[i] * Pv[j])
        if not nolc:
            for i in range(1, a + 1):
                for j in range(i, a):
                    if j + 1 <= a: gens.append(sp.expand(Pv[i] * Pv[j] - Pv[i - 1] * Pv[j + 1]))
        polys = [sp.Poly(g, *Pv) for g in gens] ; Pk = sp.Poly(key, *Pv)
        monos = sorted(set(m for p in polys + [Pk] for m in p.monoms()))
        idx = {m: t for t, m in enumerate(monos)}
        A = np.zeros((len(monos), len(polys)))
        for col, p in enumerate(polys):
            for m, v in zip(p.monoms(), p.coeffs()): A[idx[m], col] = float(v)
        bvec = np.zeros(len(monos))
        for m, v in zip(Pk.monoms(), Pk.coeffs()): bvec[idx[m]] = float(v)
        res = linprog(np.zeros(len(polys)), A_eq=A, b_eq=bvec, bounds=[(0, None)] * len(polys), method='highs')
        print(f'a={a} {kind} u={[float(x) for x in u[:4]]}: certificate {"FOUND" if res.status == 0 else "not found"}', flush=True)
