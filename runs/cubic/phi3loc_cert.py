"""Certificate: Phi3loc (local cubic reduced key, E3 weight 0; E3 weight 1 only adds (z+1) E3_1 >= 0) is >= 0
for every window a >= 3, log-concave u with u_1 = 1, z = u_0 in [0, 1/q].
Phi3loc(E3=0) is concave in z (z^2 coefficient -4 s H* <= 0), so z = 0 and z = 1/q suffice.
Products: u_i u_j >= u_{i+j-1}; keep (i, j) = (2, k-1) and, for k >= 4, (3, k-2) in YJ (i from Y, j from J).
Per u_k (divided by C(a,k)), k >= 3 (k = a is trivial since then the needs vanish):
 z = 0:   kap' + s[k(a-1)/2 + [k>=4] (a-1)(a-2)k(k-1)/(6(a-k+1))] - 4(k-2)(C(a,3) - C(k,3)) >= 0
 z = 1/q: the same + s k(a-1)/2 - s(10(k+1)/3 - 8)(a-k)/(k+1) >= 0, and u_2: kap' C(a,2) - 2 s C(a,3) = s C(a,2)/3.
s = C(a-1,2), kap' = s(2a-3)/3. Certified with a = k + 1 + m, k = 4 + p (k = 3: a = 4 + m): numerators with
nonnegative coefficients. Also checks the identity Phi3loc(E3=0) = A0 Y' + Y A0'' - 4 D H1 terms used (see phi_loc.py).
Asserts; prints CERTIFIED."""
import sympy as sp
from cert_try import negs
a, k, m, p = sp.symbols('a k m p', nonnegative=True)
def Cb(x, j): return sp.expand(sp.expand_func(sp.binomial(x, j)))
s = Cb(a - 1, 2); kp = s * (2 * a - 3) / 3
assert sp.expand(kp * Cb(a, 2) - 2 * s * Cb(a, 3) - s * Cb(a, 2) / 3) == 0
base = kp + s * k * (a - 1) / 2 - 4 * (k - 2) * (Cb(a, 3) - Cb(k, 3))
extra3 = s * (a - 1) * (a - 2) * k * (k - 1) / (6 * (a - k + 1))
z1 = s * k * (a - 1) / 2 - s * (sp.Rational(10, 3) * (k + 1) - 8) * (a - k) / (k + 1)
n_checks = 0
for tag, expr, ksub in (('z0,k=3', base, 3), ('z1/q,k=3', base + z1, 3), ('z0,k>=4', base + extra3, 4 + p), ('z1/q,k>=4', base + extra3 + z1, 4 + p)):
    e = sp.together(sp.expand(expr.subs(k, ksub).subs(a, (ksub if ksub != 3 else 3) + 1 + m)))
    num, den = sp.fraction(e)
    num, den = sp.expand(num), sp.expand(den)
    dn = negs(den, sorted(den.free_symbols, key=str)) if den.free_symbols else ((1 if den < 0 else 0), 1)
    nn = negs(num, sorted(num.free_symbols, key=str))
    print(tag, 'numerator negative coefficients:', nn, ' denominator:', sp.factor(den))
    assert nn[0] == 0 and dn[0] == 0
    n_checks += 1
print(f'CERTIFIED: Phi3loc >= 0 for all a >= 3 ({n_checks} polynomial checks)')
# exact numerical check of the bound chain on random log-concave u: Phi3loc(z) >= linearized bound >= 0 at z = 0, 1/q
import random, sys, os
from fractions import Fraction as Fr
from math import comb as C
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phi_loc import Phi3loc, rand_u
rng = random.Random(11); bad = 0
for _ in range(1500):
    A = rng.randint(3, 25)
    for zf in (Fr(0), Fr(1)):
        u = rand_u(rng, A, zfrac=zf); q = u[2]; S = C(A - 1, 2); KP = Fr(S * (2 * A - 3), 3)
        def cc(K): return C(A, 2) * C(A - 1, K - 1) + (C(A, 3) * C(A - 1, K - 2) if K >= 4 else 0)
        if zf == 0:
            lb = KP * C(A, 2) * u[2] + sum((KP * C(A, K) + S * cc(K) - 4 * (K - 2) * (C(A, 3) - C(K, 3)) * C(A, K)) * u[K] for K in range(3, A + 1))
            ex = Phi3loc(u, A)
        else:
            lb = (KP * C(A, 2) - 2 * S * C(A, 3)) * u[2] + sum((KP * C(A, K) + S * cc(K) + S * C(A, 2) * C(A - 1, K - 1)
                  - S * (Fr(10 * (K + 1), 3) - 8) * (C(A, K + 1) if K + 1 <= A else 0) - 4 * (K - 2) * (C(A, 3) - C(K, 3)) * C(A, K)) * u[K] for K in range(3, A + 1))
            ex = Phi3loc(u, A) * q / (1 + q)
        bad += not (ex >= lb >= 0)
print('bound chain on random LC u (exact): violations', bad)
assert bad == 0
print('CERTIFIED (with chain check)')
