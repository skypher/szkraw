"""Certificates for n = 2..5.
n = 4, 5: the reduction for n >= 6 applies (the n-block functional is homogeneous, and pinning u_{n-3}, u_{n-2}
to small-block values only restricts the configurations), so certify its conditions at n = 4, 5.
n = 2, 3: kappa_X = P0(z, q) + sum_{b>=3} H_b(z, q) u_b exactly (u_1 = 1, u_2 = q, u_0 = z); with u_3 = q a,
u_4 = q a y, u_5 <= q a y^2 (n = 3; y in [0, a], a in [0, q]) or u_4 <= q a^2 (n = 2), using H_top <= 0.
Usage: cert_lown.py"""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_sym import kap, l, n
from small_n_forms import forms, u as U
from cert_try import bern, negs
z, q, c, s, w, h, a, y = sp.symbols('z q c s w h a y', nonnegative=True)
TG = ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+rs']
def regimes(expr, lmin=0):
    out = {}
    for reg in ('z0', 'zl', 'zh'):
        if reg == 'z0': e = expr.subs(z, 0)
        elif reg == 'zl': e = expr.subs(z, l).subs(q, 1 / (l + w))
        else: e = expr.subs(z, h).subs(q, 1 / h).subs(l, h + w)
        num, den = sp.fraction(sp.together(sp.expand(e)))
        assert all(cf > 0 for cf in sp.Poly(den, *sorted(den.free_symbols, key=str)).coeffs()) if den.free_symbols else den > 0
        out[reg] = sp.expand(num)
    return out
def certify(num, svar=None):
    vars_ = sorted(num.free_symbols, key=str)
    if svar is not None and svar in num.free_symbols:
        bs = bern(num, svar, sp.degree(num, svar))
        tot = [negs(b, [v for v in vars_ if v != svar]) for b in bs]
        return sum(t[0] for t in tot), sum(t[1] for t in tot)
    return negs(num, vars_)
def report(tag, conds):
    res = []
    for cname, (expr, sv) in conds.items():
        for reg, num in regimes(expr).items():
            nn, nt = certify(num, sv)
            res.append(f'{cname}/{reg}:' + ('OK' if nn == 0 else f'{nn}/{nt}neg'))
    print(tag, ' '.join(res), flush=True)
for nv in (4, 5):
    for name in TG:
        g = kap(name)
        G = {j: sp.sympify(sum(v.subs(n, nv) * {0: z, 1: 1, 2: q}[aa] for (aa, jj), v in g.items() if jj == j)) for j in range(-3, 3)}
        A = G[-1] + G[-2] / q + G[-3] / q ** 2
        iii = sp.expand((A + c * G[0] + c ** 2 * G[1] + c ** 3 * G[2]).subs(c, q * s) * q ** 2)
        report(f'n={nv} {name}', {'i': (sp.expand(A * q ** 2), None), 'ii': (sp.expand((A + q * G[0]) * q ** 2), None), 'iii': (iii, s)})
for nv in (2, 3):
    F = forms(nv)
    for name in TG:
        e = sum(F[p] for p in name.split('+'))
        e = sp.expand(e.subs({U[0]: z, U[1]: 1, U[2]: q}))
        top = 5 if nv == 3 else 4
        H = {b: sp.expand(e).coeff(U[b], 1) for b in range(3, top + 1)}
        P0 = sp.expand(e.subs({U[b]: 0 for b in range(3, 8)}))
        print(f'  n={nv} {name}: H_top =', sp.factor(H[top]))
        if nv == 3:
            Fy0 = P0 + H[3] * q * a                          # y = 0: linear in a, endpoints a = 0, q
            Fyy = P0 + q * (H[3] * a + H[4] * a ** 2 + H[5] * a ** 3)  # y = a
            conds = {'a0': (P0, None), 'aq': (sp.expand(Fy0.subs(a, q)), None), 'yy': (sp.expand(Fyy.subs(a, q * s)), s)}
        else:
            Fa = P0 + q * (H[3] * a + H[4] * a ** 2)        # concave in a: endpoints
            conds = {'a0': (P0, None), 'aq': (sp.expand(Fa.subs(a, q)), None)}
        report(f'n={nv} {name}', conds)
