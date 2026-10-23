"""Planning test (float LP): cubic B-detour remainder forms rt, tt, ts, taus, ss, ttau, ttau + 7/4 rs as nonnegative
combinations of LC transfers u_{a+1}u_{b-1} - u_a u_b, (optionally) moves u_j (l u_1 - u_0), and monomials.
n = 2..5 from runs/cubic/small_n_forms.py, n >= 6 from kappa_sym.py. Usage: cubicB_lp_test2.py"""
import sys, os
import numpy as np, sympy as sp
from scipy.optimize import linprog
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic'))
from kappa_sym import kap, l as L_, n as N_
from small_n_forms import forms, u as U, l as Ls
NAMES = ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+74rs']
def form(name, lv, nv):
    F = {}
    parts = [('ttau', 1), ('rs', sp.Rational(7, 4))] if name == 'ttau+74rs' else [(name, 1)]
    for nm, w in parts:
        if nv >= 6:
            for (a, j), v in kap(nm).items():
                k = tuple(sorted((a, nv + j))); F[k] = F.get(k, 0) + float(w * v.subs({L_: lv, N_: nv}))
        else:
            P = sp.Poly(sp.expand(forms(nv)[nm].subs(Ls, lv)), *U)
            for mon, cf in zip(P.monoms(), P.coeffs()):
                idx = [i for i, e in enumerate(mon) for _ in range(e)]
                k = tuple(sorted(idx)); F[k] = F.get(k, 0) + float(w * cf)
    return F
def lp(F, lv, M, use_z):
    gens = []
    for a in range(0, M + 1):
        for b in range(a + 2, M + 1): gens.append({(a + 1, b - 1): 1.0, (a, b): -1.0})
    if use_z:
        for j in range(0, M + 1):
            g = {}; k1 = tuple(sorted((1, j))); k0 = tuple(sorted((0, j)))
            g[k1] = g.get(k1, 0) + lv; g[k0] = g.get(k0, 0) - 1.0; gens.append(g)
    for a in range(0, M + 1):
        for b in range(a, M + 1): gens.append({(a, b): 1.0})
    keys = sorted(set(k for g in gens for k in g) | set(F)); ki = {k: i for i, k in enumerate(keys)}
    A = np.zeros((len(keys), len(gens)))
    for c, g in enumerate(gens):
        for k, v in g.items(): A[ki[k], c] += v
    b = np.zeros(len(keys))
    for k, v in F.items(): b[ki[k]] += v
    return linprog(np.zeros(len(gens)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(gens), method='highs').status == 0
if __name__ == "__main__":
 for use_z in (False, True):
     print('z-moves' if use_z else 'transfers only')
     for name in NAMES:
         row = []
         for nv in (2, 3, 4, 5, 6, 8):
             s = ''
             for lv in (0, 1, 2, 3, 5, 10):
                 if (lv, nv) == (0, 2): s += '.'; continue
                 F = form(name, lv, nv)
                 s += '+' if lp(F, lv, nv + 2, use_z) else '-'
             row.append(s)
         print(f'  {name:10s}', ' '.join(row), flush=True)
