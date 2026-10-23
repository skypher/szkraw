"""Variant of bdetour_cert.py for r sigma <= u t tau: certifies only kappa_ttau + u kappa_rs (argv[1] = u); the other
coefficients do not depend on u. Original docstring:
Cubic weighted B-detour, u = 1: certificate that every coefficient form of the remainder
D - D(r,0,tau) is >= 0 off the corner (l, n) = (0, 2). Fails (AssertionError) on any rejected step.
D(l,n) = K phi_2(l) phi_n(l+1) - L c_{l+1} phi_{n+2}(l) = sum kappa_ab rho_a rho_b, rho = (r, t, tau, sigma).
Under r sigma <= t tau the remainder is >= kappa_rt rt + kappa_tt t^2 + (kappa_ttau + min(kappa_rs, 0)) t tau
+ kappa_ts t sigma + kappa_taus tau sigma + kappa_ss sigma^2, so it suffices that
  kappa_rt, kappa_tt, kappa_ts, kappa_taus, kappa_ss, kappa_ttau, kappa_ttau + kappa_rs >= 0
for all log-concave u (u_k = f_k(l)) with u_1 = 1, u_2 = q, 0 <= u_0 = z <= min(l, 1/q).
Steps: (1) block-end signs; (2) n >= 4 via the exact reduction at u_{n-1} = 1 (conditions (i)-(iii)), n = 6 + m
symbolic and n = 4, 5; (3) n = 2, 3 by the exact reduction in u_3 = q a; (4) kappa_ts at n = 2 for l >= 1.
Each polynomial condition is certified by nonnegative coefficients in the regimes z = 0, z = l (q = 1/(l + w)),
z = 1/q = h (l = h + w); condition (iii) in Bernstein form in s = c/q on [0, 1]. Where a form is not affine in z
(kappa_taus, kappa_ss at n = 2, 3: u_0 lies in both blocks) z = zeta * min(l, 1/q) with Bernstein form in zeta."""
import sys, os
from fractions import Fraction as _Fr
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_sym import kap, l, n
from small_n_forms import forms, u as U
from cert_try import bern, negs
z, q, c, s, m, w, h, a, L, H, k, zeta = sp.symbols('z q c s m w h a L H k zeta', nonnegative=True)
UU = sp.Rational(sys.argv[1]) if len(sys.argv) > 1 else sp.Integer(1)
TG = ['ttau+urs']
count = [0]
def bern_all(expr, bvars):
    # tensor Bernstein coefficients on [0,1]^k in the variables bvars
    out = [sp.expand(expr)]
    for v in bvars:
        nxt = []
        for e in out:
            nxt += bern(e, v, sp.degree(e, v)) if v in e.free_symbols else [e]
        out = nxt
    return out
def nonneg_poly(expr, svar=None):
    bvars = [] if svar is None else ([svar] if not isinstance(svar, (list, tuple)) else list(svar))
    num, den = sp.fraction(sp.together(sp.expand(expr)))
    num, den = sp.expand(num), sp.expand(den)
    if den.free_symbols: assert negs(den, sorted(den.free_symbols, key=str))[0] == 0, 'denominator'
    else: assert den > 0
    for b in bern_all(num, bvars):
        assert negs(b, sorted(b.free_symbols - set(bvars), key=str))[0] == 0, 'coefficient'
    count[0] += 1
def regimes(expr, svar=None, lshift=0):
    # affine in z: endpoints z = 0 and z = min(l, 1/q); otherwise z = zeta * min(l, 1/q), Bernstein in zeta
    bv = [] if svar is None else [svar]
    if sp.degree(sp.expand(expr), z) <= 1:
        e0, el, eh, bz = expr.subs(z, 0), expr.subs(z, l), expr.subs(z, h), bv
        nonneg_poly(e0.subs(l, l + lshift), bz)
    else:
        el, eh, bz = expr.subs(z, zeta * l), expr.subs(z, zeta * h), bv + [zeta]
    nonneg_poly(el.subs(q, 1 / (l + w)).subs(l, l + lshift), bz)
    if lshift == 0:
        nonneg_poly(eh.subs(q, 1 / h).subs(l, h + w), bz)
    else:  # l >= lshift: h >= lshift with l = h + w, or h < lshift <= l
        nonneg_poly(eh.subs(q, 1 / h).subs(l, h + w).subs(h, H + lshift), bz)
        nonneg_poly(eh.subs(q, 1 / h).subs(h, lshift / (1 + k)).subs(l, l + lshift), bz)
def kapu(name):
    if name != 'ttau+urs': return kap(name)
    out = dict(kap('ttau'))
    for k_, v in kap('rs').items(): out[k_] = sp.expand(out.get(k_, 0) + UU * v)
    return out
def blocks(name, nsub):
    g = kapu(name)
    return {j: sp.sympify(sum(v.subs(n, nsub) * {0: z, 1: 1, 2: q}[aa] for (aa, jj), v in g.items() if jj == j)) for j in range(-3, 3)}
def check_signs(G):
    # G_{-3}, G_{-2} >= 0 and G_2 <= 0 for integer l >= 0: l = 0, 1 exactly, l = 2 + L by coefficients
    for j, sg in ((-3, 1), (-2, 1), (2, -1)):
        e = sp.expand(sg * G[j])
        for lv in (0, 1):
            ev = sp.expand(e.subs(l, lv))
            if ev != 0: assert negs(ev, sorted(ev.free_symbols, key=str))[0] == 0, ('sign', j, lv)
        ev = sp.expand(e.subs(l, 2 + L))
        if ev != 0: assert negs(ev, sorted(ev.free_symbols, key=str))[0] == 0, ('sign', j)
        count[0] += 1
for name in TG:
    for nsub in (m + 6, 4, 5):
        G = blocks(name, nsub)
        assert all(sp.degree(sp.expand(G[j]), z) <= 1 for j in G if G[j] != 0)
        check_signs(G)
        A = G[-1] + G[-2] / q + G[-3] / q ** 2
        regimes(sp.expand(A * q ** 2))
        regimes(sp.expand((A + q * G[0]) * q ** 2))
        regimes(sp.expand((A + c * G[0] + c ** 2 * G[1] + c ** 3 * G[2]).subs(c, q * s) * q ** 2), s)
    for nv in (2, 3):
        e = sp.expand((forms(nv)['ttau'] + UU * forms(nv)['rs']).subs({U[0]: z, U[1]: 1, U[2]: q}))
        assert sp.Poly(e, *U[3:8]).total_degree() <= 1 and sp.degree(e, z) <= 2
        top = 5 if nv == 3 else 4
        Hb = {b: e.coeff(U[b], 1) for b in range(3, top + 1)}
        ht = sp.expand(-Hb[top])
        for lv in (0, 1): assert negs(sp.expand(ht.subs(l, lv)), [z])[0] == 0
        assert negs(sp.expand(ht.subs(l, 2 + L)), [L, z])[0] == 0
        P0 = sp.expand(e.subs({U[b]: 0 for b in range(3, 8)}))
        lsh = 1 if (nv, name) == (2, 'ts') else 0
        regimes(P0, None, lsh)
        if nv == 3:
            regimes(sp.expand(P0 + Hb[3] * q * q), None, lsh)
            regimes(sp.expand((P0 + q * (Hb[3] * a + Hb[4] * a ** 2 + Hb[5] * a ** 3)).subs(a, q * s)), s, lsh)
        else:
            regimes(sp.expand(P0 + q * (Hb[3] * q + Hb[4] * q ** 2)), None, lsh)
    print(name, 'certified', flush=True)
print(f'ALL CERTIFIED for kappa_ttau + {UU} kappa_rs ({count[0]} checks)')
