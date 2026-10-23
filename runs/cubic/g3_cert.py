"""Detour of the sigma family G3 (part of E' = W + X + V^sigma), with constant MU (argv[1], default 2).
G3_n(l) = n C(l+n-1,2) f_{n-1} + C(n,2)(l+n-2) f_{n-2} + C(n,3) f_{n-3}, G3_j(l,a) = sum_m C(m-j-1,j) C(a,m) G3_m(l).
With B_0(l,a) >= C(a,2) rho(l+1) f_2(l), c_{l+1} = rho(l+1) f_0(l+1) and C(a,2)C(a-2,n) = C(a,m)C(m,2) (m = n+2),
B_0 G3_{j-1}(l+1,a-2) >= 3 c G3_j(l,a) (j >= 2) follows from the pointwise inequality, for n >= 3,
  Pi(l,n) = (n+1)(n+2) u_2 G3_n(l+1) - MU(n-1)(u_0+u_1) G3_{n+2}(l) >= 0,
because the m-th coefficient needs C(m,2) theta_{m-2} >= MU (m-j-1)/j, and theta_{m-2} = MU (m-3)/(m(m-1)) satisfies it
for j >= 2, m >= 2j+1 (checked below; equality at j = 2).
MU = 3 fails at n = 3 (z = l = 1/q, outside the realizable profiles); the resummation needs only MU = 2.
Exact reduction as for the B-detour (u_1 = 1, u_2 = q, z = u_0 <= min(l, 1/q), n-block normalized at u_{n-1}).
Asserts every step; prints CERTIFIED."""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cert_try import bern, negs
MU = sp.Rational(sys.argv[1]) if len(sys.argv) > 1 else sp.Integer(2)
l, n = sp.symbols('l n', nonnegative=True)
z, q, c, m, w, h, a, k, j, M, J = sp.symbols('z q c m w h a k j M J', nonnegative=True)
def C(x, kk): return sp.expand(sp.expand_func(sp.binomial(x, kk)))
# weight condition: C(m,2) theta_{m-2} >= MU (m-j-1)/j with theta_{m-2} = MU (m-3)/(m(m-1))
#   <=>  j (m-3) >= 2 (m-j-1)  (= (j-2)(m-1) >= 0)  for j >= 2, m >= 2j+1
wc = sp.expand((j * (m - 3) - 2 * (m - j - 1)).subs(j, J + 2).subs(m, 2 * (J + 2) + 1 + M))
assert negs(wc, [J, M])[0] == 0
# symbolic n-block offsets: positive side u_2 * G3_n(l+1), negative side (u_0+u_1) * G3_{n+2}(l)
def g3(nn, ll, shift):  # dict offset -> coefficient, f_k(l+shift): shift 1 means u_k + u_{k+1}
    out = {}
    for i, cf in ((1, nn * C(ll + nn - 1, 2)), (2, C(nn, 2) * (ll + nn - 2)), (3, C(nn, 3))):
        offs = (-i, -i + 1) if shift else (-i,)
        for o in offs: out[o] = out.get(o, 0) + cf
    return out
pos = {o: (n + 1) * (n + 2) * cf for o, cf in g3(n, l + 1, 1).items()}            # times u_2 = q
neg = {o + 2: MU * (n - 1) * cf for o, cf in g3(n + 2, l, 0).items()}              # times (z + 1)
G = {o: sp.expand(q * pos.get(o, 0) - (z + 1) * neg.get(o, 0)) for o in range(-3, 2)}
count = [0]
def nonneg(expr, bvars=()):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    num, den = sp.expand(num), sp.expand(den)
    if den.free_symbols: assert negs(den, sorted(den.free_symbols, key=str))[0] == 0
    else: assert den > 0
    outs = [num]
    for v in bvars:
        outs = [bb for e in outs for bb in (bern(e, v, sp.degree(e, v)) if v in e.free_symbols else [e])]
    for e in outs: assert negs(e, sorted(e.free_symbols - set(bvars), key=str))[0] == 0, e
    count[0] += 1
def regimes(expr, bv=()):
    assert sp.degree(sp.expand(expr), z) <= 1
    nonneg(expr.subs(z, 0), bv)
    nonneg(expr.subs(z, l).subs(q, 1 / (l + w)), bv)
    nonneg(expr.subs(z, h).subs(q, 1 / h).subs(l, h + w), bv)
for nsub in (m + 4,):   # n >= 4: generic reduction (n = 4 pins u_{n-3}, u_{n-2} = u_1, u_2: a subset)
    Gs = {o: sp.expand(v.subs(n, nsub)) for o, v in G.items()}
    for o in (-3, -2): assert negs(Gs[o], [l, m, q, z])[0] == 0          # positive-only
    assert negs(sp.expand(-Gs[1]), [l, m, q, z])[0] == 0                   # negative-only
    A = Gs[-1] + Gs[-2] / q + Gs[-3] / q ** 2
    regimes(sp.expand(A * q ** 2))                                          # c = 0
    regimes(sp.expand((A + q * Gs[0] + q ** 2 * Gs[1]) * q ** 2))          # c = q (concave in c)
# n = 3: u_{n-3} = u_0 = z overlaps; exact in u_3 = q a, u_4 <= q a^2
U = sp.symbols('U0:6')
def val(dct, base):  # sum coefficient * u_{base + offset}
    return sum(cf * U[base + o] for o, cf in dct.items())
P3 = sp.expand((4 * 5 * U[2] * val(g3(3, l + 1, 1), 3) - 2 * MU * (U[0] + U[1]) * val({o + 2: cf for o, cf in g3(5, l, 0).items()}, 3)).subs({U[0]: z, U[1]: 1, U[2]: q}))
H3, H4 = P3.coeff(U[3], 1), P3.coeff(U[4], 1)
assert sp.Poly(P3, U[3], U[4], U[5]).total_degree() <= 1 and negs(sp.expand(-H4), [l, z])[0] == 0
P0 = sp.expand(P3.subs({U[3]: 0, U[4]: 0, U[5]: 0}))
regimes(P0); regimes(sp.expand(P0 + q * (H3 * q + H4 * q ** 2)))
print(f'CERTIFIED: G3 detour with constant {MU} ({count[0]} polynomial checks)')
