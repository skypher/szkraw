"""Planning test for the sigma-part of the cubic key (Theorem 8.17): Phi3 = u_1 Psi_3 + C(a-1,2) u_0 K with
Psi_3 = -C(a,3) u_0 Y' + Y (s X'' - C(a-1,3) D) - D (4 T_3 - E_3),  K = X Y' + Y X'' - 4 D H*,  s = C(a-1,2),
D = u_0 + u_1 (u_k = f_k(l)). Bounding u_0^2 H* <= u_0 u_1 H*_shift (u_0 u_{n} <= u_1 u_{n-1}) gives
Phi3 >= u_1 A + u_0 B with A = Psi_3|_{u_0=0} and B = u_1 Psi_3^1 + s K^0 - 4 s u_1 H*_shift, both quadratic forms.
Tests by float LP (LC transfers + monomials) whether A >= 0 and B >= 0 on LC sequences, for a = 3..14; and the
tail sums (transfers only, per index sum) symbolically. Usage: phi3_test.py"""
import sys, os
import numpy as np, sympy as sp
from math import comb as C
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cubicB_lp_test2 import lp

def forms(a):
    U = sp.symbols(f'u0:{a + 2}')
    u = lambda k: U[k] if 0 <= k <= a + 1 else 0
    s = C(a - 1, 2)
    X = sum(C(a, n) * u(n) for n in range(1, a + 1))
    Xpp = sum((C(a - 1, n) - (1 if n == 1 else 0)) * u(n) for n in range(1, a))
    Y = sum(C(a, n) * u(n) for n in range(2, a + 1))
    Yp = sum(C(a - 1, n) * (u(n) + u(n + 1)) for n in range(2, a))
    Hs = sum((n - 2) * C(a, n) * u(n) for n in range(3, a + 1))
    Hsh = sum((n - 2) * C(a, n) * u(n - 1) for n in range(3, a + 1))
    T3 = sum((n - 2) * C(a, n) * (C(a, 3) - C(n, 3)) * u(n) for n in range(3, a + 1))
    E3 = sum((n - 2) * C(a, n) * C(n, 3) * (3 * u(n - 1) + 3 * u(n - 2) + u(n - 3)) for n in range(3, a + 1))
    D = u(0) + u(1)
    Psi3 = -C(a, 3) * u(0) * Yp + Y * (s * Xpp - C(a - 1, 3) * D) - D * (4 * T3 - E3)
    Psi3 = sp.expand(Psi3)
    A = sp.expand(Psi3.subs(U[0], 0))
    Psi1 = sp.expand((Psi3 - A) / U[0])
    K0 = sp.expand(X * Yp + Y * Xpp - 4 * U[1] * Hs)
    B = sp.expand(U[1] * Psi1 + s * K0 - 4 * s * U[1] * Hsh)
    return U, A, B
def to_dict(F, U):
    P = sp.Poly(F, *U); out = {}
    for mon, c in zip(P.monoms(), P.coeffs()):
        idx = tuple(sorted(i for i, e in enumerate(mon) for _ in range(e)))
        out[idx] = out.get(idx, 0) + float(c)
    return out
for a in range(3, 15):
    U, A, B = forms(a)
    ra = lp(to_dict(A, U), 0, a + 1, False) if A != 0 else True
    rb = lp(to_dict(B, U), 0, a + 1, False) if B != 0 else True
    print(f'a={a}: A by transfers {"OK" if ra else "FAIL"}, B by transfers {"OK" if rb else "FAIL"}', flush=True)
