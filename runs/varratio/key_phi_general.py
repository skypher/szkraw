"""General coefficient formulas of Phi, checked symbolically. With c^(k)(n) = C(n,k) d_{l+n}:
phi_0k = K delta_k + F [4 D Z1^(k) + 2 D V1^(k) - Y C_X'^(k) - Y' C_X^(k)]  (k >= 1),
phi_km = B0'^(k) [X delta_m - F C_X^(m)] + B0'^(m) [X delta_k - F C_X^(k)] + B0^(k) [X' delta_m - F C_X'^(m)]
         + B0^(m) [X' delta_k - F C_X'^(k)]  (k, m >= 2; phi_kk is half of the symmetric sum).
Usage: key_phi_general.py amax"""
import sys, math
import sympy as sp
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_phi import parts
C = math.comb
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1)); u = list(U) + [sp.Integer(0)] * 3
    P, Lin, Quad, f1, Dc = parts(u, a)
    Phi = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
    d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
    ck = lambda k, n: C(n, k) * d(n)
    X = d(a) - d(0); Xp = d(a - 1) - d(1); D = d(1); F = d(a) - d(a - 1)
    Y = sum(C(a, n) * u[n] for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
    Hs = sum((n - 2) * C(a, n) * u[n] for n in range(3, a + 1)); K = X * Yp + Y * Xp - 4 * D * Hs
    B0 = lambda k: ck(k, a) - ck(k, 0) - a * (ck(k, 1) - ck(k, 0))
    B0p = lambda k: ck(k, a) - ck(k, 1) - (a - 1) * (ck(k, 2) - ck(k, 1))
    CX = lambda k: ck(k, a) - ck(k, 0); CXp = lambda k: ck(k, a - 1) - ck(k, 1); dl = lambda k: ck(k, a) - ck(k, a - 1)
    Z1 = lambda k: sum((n - 2) * C(a, n) * C(n, k) * u[n] for n in range(3, a + 1))
    V1 = lambda k: sum((n - 2) * C(a, n) * n * (C(n, k) - C(n - 1, k)) * u[n - 1] for n in range(3, a + 1))
    ok0 = all(sp.expand(K * dl(k) + F * (4 * D * Z1(k) + 2 * D * V1(k) - Y * CXp(k) - Yp * CX(k)) - Phi.coeff_monomial(P[0] * P[k])) == 0
              for k in range(1, a + 1))
    okkm = True
    for k in range(2, a + 1):
        for m in range(k, a + 1):
            g = B0p(k) * (X * dl(m) - F * CX(m)) + B0p(m) * (X * dl(k) - F * CX(k)) + B0(k) * (Xp * dl(m) - F * CXp(m)) + B0(m) * (Xp * dl(k) - F * CXp(k))
            if k == m: g = g / 2
            if sp.expand(g - Phi.coeff_monomial(P[k] * P[m])) != 0: okkm = False
    print(f'a={a}: phi_0k formula {"OK" if ok0 else "FAILS"}; phi_km (k,m>=2) determinant formula {"OK" if okkm else "FAILS"}', flush=True)
