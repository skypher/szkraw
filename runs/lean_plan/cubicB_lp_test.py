"""Test: is each cubic B-detour coefficient form kappa (runs/cubic/kappa_sym.py, n >= 6) a nonnegative combination of
LC transfers u_{a+1}u_{b-1} - u_a u_b, moves u_j (l u_1 - u_0), and monomials, at numeric (l, n)?
Float LP feasibility only (a planning test). Usage: cubicB_lp_test.py"""
import sys, os, itertools
import numpy as np, sympy as sp
from scipy.optimize import linprog
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic'))
from kappa_sym import kap, l, n
def form(name, lv, nv):
    g = kap(name); F = {}
    for (a, j), v in g.items():
        F[(a, nv + j)] = F.get((a, nv + j), 0) + float(v.subs({l: lv, n: nv}))
    return F
def lp(F, lv, nv, use_z=True):
    idx = sorted(set(i for p in F for i in p) | set(range(0, nv + 3)))
    M = max(idx)
    gens = []
    for a in range(0, M + 1):
        for b in range(a + 2, M + 1):
            gens.append({(a + 1, b - 1): 1.0, (a, b): -1.0})
    if use_z:
        for j in range(0, M + 1):
            g = {}
            g[tuple(sorted((1, j)))] = g.get(tuple(sorted((1, j))), 0) + lv
            g[tuple(sorted((0, j)))] = g.get(tuple(sorted((0, j))), 0) - 1.0
            gens.append(g)
    for a in range(0, M + 1):
        for b in range(a, M + 1): gens.append({(a, b): 1.0})
    keys = sorted(set(k for g in gens for k in g) | set(tuple(sorted(k)) for k in F))
    ki = {k: i for i, k in enumerate(keys)}
    A = np.zeros((len(keys), len(gens)))
    for c, g in enumerate(gens):
        for k, v in g.items(): A[ki[k], c] += v
    b = np.zeros(len(keys))
    for k, v in F.items(): b[ki[tuple(sorted(k))]] += v
    res = linprog(np.zeros(len(gens)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(gens), method='highs')
    return res.status == 0
for name in ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+rs']:
    out = []
    for lv in (0, 1, 2, 3, 5, 10):
        for nv in (6, 7, 9, 12):
            out.append(('+' if lp(form(name, lv, nv), lv, nv) else '-'))
    print(name, ''.join(out), flush=True)
print('without z-moves:')
for name in ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+rs', 'rr', 'rtau', 'tautau']:
    out = []
    for lv in (0, 1, 2, 3, 5, 10):
        for nv in (6, 7, 9, 12):
            out.append(('+' if lp(form(name, lv, nv), lv, nv, use_z=False) else '-'))
    print(name, ''.join(out), flush=True)
