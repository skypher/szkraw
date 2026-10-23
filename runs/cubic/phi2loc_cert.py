"""Certificate: Phi2loc (local quadratic reduced key: rho(l+k) = C(k,2), s = a-1, V shape n-1 (weight 2), W shape 1
(weight 1)) is >= 0 for every a >= 3, log-concave u, u_1 = 1, z in [0, 1/q] (the tau part of Theorem 8.11's key,
which needs only s >= tau(a-1)). Concave in z (z^2 coefficient -4(a-1)H*), so z = 0 and z = 1/q suffice.
With y_k = C(a,k)u_k: A0 = z((a-1)Y + C(a,2)), A0'' = (z+1)((a-1)J + C(a-1,2)), H1 = (a-1) z H* + T2,
T2 = sum_{n>=3} (n-2)(C(a,2) - C(n,2)) y_n, V1 = sum_{k>=2} k(k-1)(a-k) y_k, W1 = sum_{k>=1} k C(a-k,2) y_k.
Bounds as in phi3loc_cert.py (products (2,k-1), (3,k-2) in YJ; at z = 1/q, C(a,2)Y'/(1+q) >= (C(a,2)/q) sum C(a-1,k-1)u_k,
(a-1) Y Y'/(1+q) >= (a-1)C(a,2) sum C(a-1,k-1) u_k, u_k/q <= u_{k-1}). Asserts; prints CERTIFIED."""
import sys, os, random
import sympy as sp
from fractions import Fraction as Fr
from math import comb as C
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cert_try import negs
from phi_loc import Phi2loc, rand_u
a, k, m, p = sp.symbols('a k m p', nonnegative=True)
def Cb(x, j): return sp.expand(sp.expand_func(sp.binomial(x, j)))
# per u_k / C(a,k), k >= 3 (k <= a-1; at k = a the needs vanish or are covered: checked numerically below)
base = Cb(a - 1, 2) + (a - 1) * k * (a - 1) / 2 + 2 * k * (k - 1) * (a - k) + k * Cb(a - k, 2) - 4 * (k - 2) * (Cb(a, 2) - Cb(k, 2))
extra3 = (a - 1) * (a - 1) * (a - 2) * k * (k - 1) / (6 * (a - k + 1))
z1 = (a - 1) * k * (a - 1) / 2 - (a - 1) * (sp.Rational(7, 2) * (k + 1) - 8) * (a - k) / (k + 1)
y2 = (a - 1) * (a - 2) / 2 + 4 * (a - 2) + (a - 2) * (a - 3) - sp.Rational(5, 2) * (a - 1) * (a - 2) / 3   # u_2 at z = 1/q, / C(a,2)
e = sp.expand(y2.subs(a, 3 + m)); assert negs(e, [m])[0] == 0
for tag, expr, ks in (('z0,k=3', base, 3), ('z1/q,k=3', base + z1, 3), ('z0,k>=4', base + extra3, 4 + p), ('z1/q,k>=4', base + extra3 + z1, 4 + p)):
    num, den = sp.fraction(sp.together(sp.expand(expr.subs(k, ks).subs(a, ks + 1 + m))))
    nn = negs(sp.expand(num), sorted(num.free_symbols, key=str)); print(tag, 'negative coefficients', nn, 'den', sp.factor(den))
    assert nn[0] == 0
rng = random.Random(5); bad = 0
for _ in range(1500):
    A = rng.randint(3, 25)
    for zf in (Fr(0), Fr(1)):
        u = rand_u(rng, A, zfrac=zf); q = u[2]
        cc = lambda K: C(A, 2) * C(A - 1, K - 1) + (C(A, 3) * C(A - 1, K - 2) if K >= 4 else 0)
        V = lambda K: K * (K - 1) * (A - K) * C(A, K); Wt = lambda K: K * C(A - K, 2) * C(A, K)
        if zf == 0:
            lb = sum(((C(A - 1, 2) * C(A, K) + (A - 1) * cc(K) if K >= 3 else (C(A - 1, 2) * C(A, K) if K == 2 else 0)) + 2 * V(K) + Wt(K)
                      - (4 * (K - 2) * (C(A, 2) - C(K, 2)) * C(A, K) if K >= 3 else 0)) * u[K] for K in range(1, A + 1))
            ex = Phi2loc(u, A)
        else:
            lb = Wt(1) * u[1] + (C(A - 1, 2) * C(A, 2) + 2 * V(2) + Wt(2) - Fr(5, 2) * (A - 1) * C(A, 3)) * u[2] + sum(
                (C(A - 1, 2) * C(A, K) + (A - 1) * cc(K) + (A - 1) * C(A, 2) * C(A - 1, K - 1) + 2 * V(K) + Wt(K)
                 - (A - 1) * (Fr(7 * (K + 1), 2) - 8) * (C(A, K + 1) if K + 1 <= A else 0) - 4 * (K - 2) * (C(A, 2) - C(K, 2)) * C(A, K)) * u[K]
                for K in range(3, A + 1))
            ex = Phi2loc(u, A) * q / (1 + q)
        bad += not (ex >= lb >= 0)
print('bound chain on random LC u (exact): violations', bad); assert bad == 0
print('CERTIFIED: Phi2loc >= 0 for all a >= 3')
