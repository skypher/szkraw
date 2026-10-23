"""Check Phi = B0' E1 + B0 E2 + c_{l+1} E3 and the closed forms
E1 = s_{a-1} d_{l+a}(d_{l+a-1} - d_l) - (rho(l+a-1) - rho(l)) d_l F,
E2 = s_{a-1} d_{l+a}(d_{l+a-1} - d_{l+1}) - (rho(l+a-1) - rho(l+1)) d_{l+1} F,
E3 = 2 F V1 - 4 sum_{n>=3} (n-2) y_n [F (rho(l+a) - rho(l+n)) + s_{a-1} d_{l+a-1}],
symbolically in u and P, a = 3..amax. Usage: key_phi_E.py amax"""
import sys, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
C = math.comb
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1)); u = list(U) + [sp.Integer(0)] * 3
    P, Lin, Quad, f1, Dc = parts(u, a)
    Phi = sp.expand(Lin * Dc - f1 * Quad)
    rho = lambda n: sum(C(n, k) * P[k] for k in range(min(n, a) + 1))
    d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1)); c = lambda n: rho(n) * d(n)
    X = d(a) - d(0); Xp = d(a - 1) - d(1); F = d(a) - d(a - 1); Dcc = c(a) - c(a - 1)
    B0 = c(a) - c(0) - a * (c(1) - c(0)); B0p = c(a) - c(1) - (a - 1) * (c(2) - c(1))
    Hs = sum((n - 2) * C(a, n) * u[n] for n in range(3, a + 1))
    Z1 = sum((n - 2) * C(a, n) * rho(n) * u[n] for n in range(3, a + 1))
    V1 = sum((n - 2) * C(a, n) * n * (rho(n) - rho(n - 1)) * u[n - 1] for n in range(3, a + 1))
    E1 = X * Dcc - F * (c(a) - c(0)); E2 = Xp * Dcc - F * (c(a - 1) - c(1)); E3 = 4 * F * Z1 + 2 * F * V1 - 4 * Hs * Dcc
    ok1 = sp.expand(B0p * E1 + B0 * E2 + c(1) * E3 - Phi) == 0
    s_top = rho(a) - rho(a - 1)
    E1c = s_top * d(a) * (d(a - 1) - d(0)) - (rho(a - 1) - rho(0)) * d(0) * F
    E2c = s_top * d(a) * (d(a - 1) - d(1)) - (rho(a - 1) - rho(1)) * d(1) * F
    E3c = 2 * F * V1 - 4 * sum((n - 2) * C(a, n) * u[n] * (F * (rho(a) - rho(n)) + s_top * d(a - 1)) for n in range(3, a + 1))
    ok2 = all(sp.expand(x - y) == 0 for x, y in [(E1, E1c), (E2, E2c), (E3, E3c)])
    print(f'a={a}: Phi = B0p E1 + B0 E2 + c1 E3 {"OK" if ok1 else "FAILS"}; closed forms of E1, E2, E3 {"OK" if ok2 else "FAIL"}', flush=True)
