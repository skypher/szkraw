"""Parametric certificate search for the cubic B form F = kappa_ttau + 7/4 kappa_rsigma at n = 2..5 (planning):
generators = LC transfers u_{a+1}u_{b-1} - u_a u_b, moves u_j (l u_1 - u_0), monomials. Take the support of a basic
LP solution at a large l, solve the restricted system symbolically in l, and report from which l on all multipliers
are >= 0 (and whether the support is the same at another large l). Usage: cubicB74_param.py"""
import sys, os
import numpy as np, sympy as sp
from scipy.optimize import linprog
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic'))
from kappa_sym import kap, l as L_, n as N_
L = sp.Symbol('L', positive=True)
def form_sym(nv):
    F = {}
    for p, w in (('ttau', 1), ('rs', sp.Rational(7, 4))):
        for (a, j), v in kap(p).items():
            b = nv + j
            if b < 0: continue
            k = tuple(sorted((a, b))); F[k] = sp.expand(F.get(k, 0) + w * v.subs({N_: nv, L_: L}))
    return {k: v for k, v in F.items() if v != 0}
def gens(M):
    G = []
    for a in range(0, M + 1):
        for b in range(a + 2, M + 1): G.append(('T', a, b, {(a + 1, b - 1): sp.Integer(1), (a, b): sp.Integer(-1)}))
    for j in range(0, M + 1):
        g = {}; k1 = tuple(sorted((1, j))); k0 = tuple(sorted((0, j)))
        g[k1] = g.get(k1, 0) + L; g[k0] = g.get(k0, 0) - 1
        G.append(('Z', j, None, g))
    for a in range(0, M + 1):
        for b in range(a, M + 1): G.append(('M', a, b, {(a, b): sp.Integer(1)}))
    return G
def basic_support(F, G, lv):
    keys = sorted(set(k for g in G for k in g[3]) | set(F)); ki = {k: i for i, k in enumerate(keys)}
    A = np.zeros((len(keys), len(G)))
    for c, g in enumerate(G):
        for k, v in g[3].items(): A[ki[k], c] += float(sp.sympify(v).subs(L, lv))
    b = np.zeros(len(keys))
    for k, v in F.items(): b[ki[k]] += float(v.subs(L, lv))
    res = linprog(np.zeros(len(G)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(G), method='highs-ds')
    return keys, [c for c in range(len(G)) if res.x[c] > 1e-9]
for nv in (2, 3, 4, 5):
    F = form_sym(nv); G = gens(nv + 2)
    keys, S1 = basic_support(F, G, 1000)
    _, S2 = basic_support(F, G, 300)
    xs = sp.symbols(f'x0:{len(S1)}')
    eqs = []
    for k in keys:
        eqs.append(sp.Eq(sum(xs[i] * G[c][3].get(k, 0) for i, c in enumerate(S1)), F.get(k, 0)))
    sol = sp.solve(eqs, xs, dict=True)
    if not sol: print(f'n={nv}: no symbolic solution on the support'); continue
    sol = sol[0]
    free = [x for x in xs if x not in sol]
    sol = {x: sp.factor(sol.get(x, x)) for x in xs}
    # threshold: largest positive real root of numerators/denominators
    lmin = 0
    for x, v in sol.items():
        num, den = sp.fraction(sp.together(v))
        for poly in (num, den):
            if poly.has(L):
                rts = [r for r in sp.Poly(poly, L).nroots() if abs(sp.im(r)) < 1e-9 and sp.re(r) > 0]
                if rts: lmin = max(lmin, max(float(sp.re(r)) for r in rts))
    ok_big = all(float(v.subs(L, 1e6)) >= -1e-12 for v in sol.values() if not v.free_symbols - {L})
    print(f'n={nv}: support {len(S1)} (same at l=300: {set(S1) == set(S2)}), free vars {len(free)}, '
          f'nonneg at l=1e6: {ok_big}, sign changes below l ~ {lmin:.2f}', flush=True)
