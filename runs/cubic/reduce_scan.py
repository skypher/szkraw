"""Exact reduction of each coefficient form kappa_X (n >= 6) to one-variable conditions.
Normalize u_1 = 1, u_2 = q, u_0 = z in [0, min(l, 1/q)], and the n-block at u_{n-1} = 1. Then u_{n-2} >= 1/q,
u_{n-3} >= 1/q^2 (attained), u_n = c in [0, q], u_{n+1} = c y, u_{n+2} <= c y^2 with y in [0, c].
With G_j = sum_a g_{a,j} u_a: if G_{-3}, G_{-2} >= 0 and G_2 <= 0, kappa_X >= A + c (G_0 + G_1 y + G_2 y^2),
A = G_{-1} + G_{-2}/q + G_{-3}/q^2, concave in y; so kappa_X >= 0 for all configurations iff
  (i) A >= 0, (ii) A + q G_0 >= 0, (iii) A + c G_0 + c^2 G_1 + c^3 G_2 >= 0 on [0, q], at z = 0 and z = zmax.
Scan: l <= lmax, 6 <= n <= nmax, q log-grid, c grid. Usage: reduce_scan.py lmax nmax"""
import sys, os
import numpy as np
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_sym import kap, l, n
lmax, nmax = int(sys.argv[1]), int(sys.argv[2])
z, q, c = sp.symbols('z q c', positive=True)
TG = ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+rs']
qs = np.exp(np.linspace(np.log(1e-4), np.log(1e4), 161))
cs = np.linspace(0, 1, 101)
for name in TG:
    g = kap(name)
    G = {j: sp.sympify(sum(v * {0: z, 1: 1, 2: q}[a] for (a, jj), v in g.items() if jj == j)) for j in range(-3, 3)}
    # sign checks of block-end coefficients (polynomials in l, n, z, q, all variables >= 0, n >= 6)
    sgn = {}
    for j, want in ((-3, 1), (-2, 1), (2, -1)):
        P = sp.Poly(sp.expand(want * G[j].subs(n, n + 6)) + sp.Symbol("e") ** 0 * 0, l, n, z, q) if G[j] != 0 else None
        sgn[j] = True if P is None else all(cf >= 0 for cf in P.coeffs())
    A = G[-1] + G[-2] / q + G[-3] / q ** 2
    f1 = sp.lambdify((l, n, z, q), A, 'numpy')
    f2 = sp.lambdify((l, n, z, q), A + q * G[0], 'numpy')
    f3 = sp.lambdify((l, n, z, q, c), A + c * G[0] + c ** 2 * G[1] + c ** 3 * G[2], 'numpy')
    sc = sp.lambdify((l, n, z, q), abs(G[-1]) + abs(G[-2]) / q + abs(G[-3]) / q ** 2 + q * abs(G[0]) + q * q * abs(G[1]) + q ** 3 * abs(G[2]), 'numpy')
    worst = [(1e9, None)] * 3
    for lv in range(0, lmax + 1):
        for nv in range(6, nmax + 1):
            for zmode in (0, 1):
                zv = np.minimum(lv, 1 / qs) if zmode else 0 * qs
                s = sc(lv, nv, zv, qs) + 1e-300
                v1 = f1(lv, nv, zv, qs) / s; v2 = f2(lv, nv, zv, qs) / s
                v3 = np.min(np.array([f3(lv, nv, zv, qs, cc * qs) for cc in cs]), axis=0) / s
                for k, v in enumerate((v1, v2, v3)):
                    i = int(np.argmin(v))
                    if v[i] < worst[k][0]: worst[k] = (float(v[i]), (lv, nv, zmode, float(qs[i])))
    print(f'{name}: signs G-3>=0 {sgn[-3]}, G-2>=0 {sgn[-2]}, G2<=0 {sgn[2]}; worst (i) {worst[0][0]:.2e} {worst[0][1]}, (ii) {worst[1][0]:.2e} {worst[1][1]}, (iii) {worst[2][0]:.2e} {worst[2][1]}', flush=True)
