"""Certificate for the detour of the merged family E (constant MU = 3) of the cubic route at u = 1.
E_n = C(n,2)(tau + sigma l) f_{n-2} + sigma C(n,3)(3 f_{n-1} + 3 f_{n-2} + f_{n-3}).
Pointwise (n >= 3): P(l,n) = (n+1)(n+2)(phi_2(l) + (n/3) phi_3(l)) E_n(l+1) - MU (n-1) c_{l+1} E_{n+2}(l) >= 0
(edetour_polar.py explains why this gives B_0 E_{j-1}(l+1,a-2) >= MU c E_j(l,a) for j >= 2).
Polarized in rho = (r,t,tau,sigma); with r sigma <= t tau it suffices that
k_rtau, k_ttau, k_ttau + k_rs, k_ts, k_tautau, k_taus, k_ss >= 0 (k_rs itself may be negative).
Each is bilinear in the small block (u_0..u_3) = (z, 1, q, q x) (x = u_3/u_2 <= q) and the n-block u_{n-3}..u_{n+1}.
n >= 5: the n-block functional is homogeneous with ratios <= x; normalize u_{n-1} = 1; u_{n-2} >= 1/x, u_{n-3} >= 1/x^2
(coefficients G_{-3}, G_{-2} >= 0), u_n = c in [0, x], u_{n+1} <= c^2 (G_1 <= 0); concave in c: c = 0 and c = x.
n = 3, 4: exact (u_4 = q x y, u_5 <= q x y^2 for n = 4, concave in y; u_4 <= q x^2 for n = 3).
Regimes for z as in bdetour_cert.py; x = q s with Bernstein form in s (and in zeta where z is not affine).
Asserts every step; prints CERTIFIED."""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cert_try import bern, negs
MU = sp.Rational(sys.argv[1]) if len(sys.argv) > 1 else sp.Integer(3)
l, n = sp.symbols('l n', nonnegative=True)
z, q, x, c, s, m, w, h, y, zeta, L = sp.symbols('z q x c s m w h y zeta L', nonnegative=True)
def Cb(X, k): return sp.expand(sp.expand_func(sp.binomial(X, k))) if k >= 0 else 0
def smallphi(m_, b):  # phi_m[e_b](l) as {small index: coefficient}
    return {m_ - i: sp.binomial(m_, i) * Cb(l + m_ - i, b - i) for i in range(0, min(b, m_) + 1)}
def small(b):  # phi_2 + (n/3) phi_3, as {index: coeff}
    out = dict(smallphi(2, b))
    for k_, v in smallphi(3, b).items(): out[k_] = out.get(k_, 0) + n / 3 * v
    return out
def cvec(b): return {0: Cb(l + 1, b), 1: Cb(l + 1, b)}
def Eblock(part, nn, ll, shift):  # E^part_nn(ll) as {offset rel. n: coeff}; shift: f(l+1) = u_k + u_{k+1}
    terms = []
    if part == 'tau': terms = [(2, Cb(nn, 2))]
    else: terms = [(2, ll * Cb(nn, 2) + 3 * Cb(nn, 3)), (1, 3 * Cb(nn, 3)), (3, Cb(nn, 3))]
    out = {}
    for i, cf in terms:
        base = nn - i - n  # offset of f_{nn-i}
        for o in ((base, base + 1) if shift else (base,)):
            out[o] = out.get(o, 0) + cf
    return out
B = {0: 'r', 1: 't', 2: 'tau', 3: 's'}
def kappa():
    acc = {}
    for b in range(4):
        for part, g in (('tau', 2), ('sig', 3)):
            key = tuple(sorted((b, g)))
            d = acc.setdefault(key, {})
            pos = Eblock(part, n, l + 1, True); neg = Eblock(part, n + 2, l, False)
            for a_, x1 in small(b).items():
                for o, x2 in pos.items(): d[(a_, o)] = d.get((a_, o), 0) + (n + 1) * (n + 2) * x1 * x2
            for a_, x1 in cvec(b).items():
                for o, x2 in neg.items(): d[(a_, o)] = d.get((a_, o), 0) - MU * (n - 1) * x1 * x2
    return acc
K = kappa()
def comb(*keys):
    out = {}
    for kk in keys:
        for k_, v in K.get(kk, {}).items(): out[k_] = out.get(k_, 0) + v
    return out
TG = {'rtau': [(0, 2)], 'ttau': [(1, 2)], 'ttau+rs': [(1, 2), (0, 3)], 'ts': [(1, 3)], 'tautau': [(2, 2)], 'taus': [(2, 3)], 'ss': [(3, 3)]}
SB = {0: z, 1: 1, 2: q, 3: q * x}
count = [0]
def nonneg(expr, bvars):
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    num, den = sp.expand(num), sp.expand(den)
    if den.free_symbols: assert negs(den, sorted(den.free_symbols, key=str))[0] == 0, 'den'
    else: assert den > 0
    outs = [num]
    for v in bvars:
        outs = [bb for e_ in outs for bb in (bern(e_, v, sp.degree(e_, v)) if v in e_.free_symbols else [e_])]
    for e_ in outs: assert negs(e_, sorted(e_.free_symbols - set(bvars), key=str))[0] == 0, e_
    count[0] += 1
def regimes(expr, bv):
    expr = sp.expand(expr.subs(x, q * s))
    bv = list(bv) + [s]
    if sp.degree(expr, z) <= 1:
        nonneg(expr.subs(z, 0), bv); el, eh, bz = expr.subs(z, l), expr.subs(z, h), bv
    else:
        el, eh, bz = expr.subs(z, zeta * l), expr.subs(z, zeta * h), bv + [zeta]
    nonneg(el.subs(q, 1 / (l + w)), bz)
    nonneg(eh.subs(q, 1 / h).subs(l, h + w), bz)
for name, keys in TG.items():
    g = comb(*keys)
    for nsub in (m + 5,):
        G = {j: sp.expand(sum(v.subs(n, nsub) * SB[a_] for (a_, jj), v in g.items() if jj == j)) for j in range(-3, 2)}
        for j, sg in ((-3, 1), (-2, 1), (1, -1)):
            e_ = sp.expand(sg * G[j])
            for lv in (0, 1, 2):
                ev = sp.expand(e_.subs(l, lv))
                if ev != 0: assert negs(sp.expand(ev.subs(x, q * s)), sorted(ev.free_symbols | {s} - {x}, key=str))[0] == 0, (name, j, lv)
            ev = sp.expand(e_.subs(l, 3 + L).subs(x, q * s))
            if ev != 0: assert negs(ev, sorted(ev.free_symbols, key=str))[0] == 0, (name, j)
            count[0] += 1
        A2 = sp.expand(G[-1] * x ** 2 + G[-2] * x + G[-3])                   # A x^2
        regimes(A2, [])
        regimes(sp.expand(A2 + (G[0] * x + G[1] * x ** 2) * x ** 2), [])    # (A + G0 x + G1 x^2) x^2
    # n = 3, 4 exact
    for nv in (3, 4):
        U = sp.symbols('U0:9')
        e_ = 0
        for (a_, o), v in g.items():
            e_ += v.subs(n, nv) * SB[a_] * U[nv + o]
        e_ = sp.expand(e_.subs({U[0]: z, U[1]: 1, U[2]: q, U[3]: q * x}))
        if nv == 4:
            H5 = e_.coeff(U[5], 1); assert sp.Poly(e_, U[4], U[5]).total_degree() <= 1
            for lv in (0, 1, 2):
                hv = sp.expand(-H5.subs(l, lv))
                if hv != 0: assert negs(hv, sorted(hv.free_symbols, key=str))[0] == 0
            assert negs(sp.expand(-H5.subs(l, 3 + L)), sorted(H5.free_symbols - {l} | {L}, key=str))[0] == 0
            Fy = sp.expand(e_.subs({U[4]: q * x * y, U[5]: q * x * y ** 2}))     # concave in y on [0, x]
            regimes(Fy.subs(y, 0), []); regimes(Fy.subs(y, x), [])
        else:
            H4 = e_.coeff(U[4], 1); assert sp.Poly(e_, U[4]).total_degree() <= 1
            for lv in (0, 1, 2):
                hv = sp.expand(-H4.subs(l, lv))
                if hv != 0: assert negs(sp.expand(hv.subs(x, q * s)), sorted(hv.free_symbols | {s} - {x}, key=str))[0] == 0
            assert negs(sp.expand(-H4.subs(l, 3 + L).subs(x, q * s)), sorted((H4.free_symbols - {l, x}) | {L, s}, key=str))[0] == 0
            regimes(sp.expand(e_.subs(U[4], q * x ** 2)), [])
    print(name, 'certified', flush=True)
print(f'CERTIFIED: E detour with constant {MU} ({count[0]} checks)')
