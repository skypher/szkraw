"""Closed form of the sigma = 1 coefficient phi_01 of Phi (coefficient of P_0 P_1), checked symbolically for a = 3..amax:
phi_01 = K d_a + F [4 D sum_{n=3}^a (n-2)(n-a+1) C(a,n) u_n + 2 D sum_{n=3}^a (n-2) n C(a,n) u_{n-1}
                    - Y'(d_a + (a-1) u_0) - (a-2) Y D],
K = X Y' + Y X' - 4 D H_*, F = d_{l+a} - d_{l+a-1}, D = d_{l+1}. Usage: key_phi01.py amax"""
import sys, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
C = math.comb
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1)); u = list(U) + [sp.Integer(0)] * 3
    P, Lin, Quad, f1, Dc = parts(u, a)
    Phi = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
    phi01 = Phi.coeff_monomial(P[0] * P[1])
    d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
    f1n = lambda l: sum(C(l, m) * u[m + 1] for m in range(l + 1))  # f_n(l+1) for n = 1 not needed
    X = d(a) - d(0); Xp = d(a - 1) - d(1); D = d(1); da = d(a); F = d(a) - d(a - 1)
    Y = sum(C(a, n) * u[n] for n in range(2, a + 1))
    Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
    Hs = sum((n - 2) * C(a, n) * u[n] for n in range(3, a + 1))
    K = X * Yp + Y * Xp - 4 * D * Hs
    br = 4 * D * sum((n - 2) * (n - a + 1) * C(a, n) * u[n] for n in range(3, a + 1)) \
        + 2 * D * sum((n - 2) * n * C(a, n) * u[n - 1] for n in range(3, a + 1)) - Yp * (da + (a - 1) * u[0]) - (a - 2) * Y * D
    guess = sp.expand(K * da + F * br)
    print(f'a={a}: closed form {"MATCHES" if sp.expand(guess - phi01) == 0 else "differs"}', flush=True)
