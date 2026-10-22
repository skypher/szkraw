"""LP certificate search for w^2 L_k(1/w) >= 0 (w = u_2, u_1 = 1, u_0 = 1/w): nonnegative combination of
G1(i,j) = u_i u_j - u_{i+j-1} (2 <= i <= j), G2(n) = u_2 u_{n-1} - u_n (n >= 3), u_2*G1, u_2*G2, and monomials.
Usage: key_zmax_lp.py amax"""
import sys, math, itertools
import sympy as sp
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_extreme import L
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    us = sp.symbols('u2:%d' % (a + 3)); w = us[0]; top = a + 2
    U = lambda n: sp.Integer(1) if n == 1 else (1 / w if n == 0 else (us[n - 2] if n <= top else sp.Integer(0)))
    gens = []
    for i in range(2, top + 1):
        for j in range(i, top + 1):
            if i + j - 1 <= top: gens.append(U(i) * U(j) - U(i + j - 1))
    for n in range(3, top + 1): gens.append(U(2) * U(n - 1) - U(n))
    gens = gens + [sp.expand(w * g) for g in gens]
    for k in range(0, a):
        s = [sp.Integer(math.comb(i, k)) for i in range(a)]
        uu = [U(n) for n in range(top + 1)]
        target = sp.expand(sp.cancel(L(uu, a, s[a - 1] / w, s, sp.Integer(2)) * w ** 2))
        polys = [sp.Poly(sp.expand(g), *us) for g in gens]
        Pt = sp.Poly(target, *us)
        monos = sorted(set(m for p in polys + [Pt] for m in p.monoms()))
        idx = {m: t for t, m in enumerate(monos)}
        A = np.zeros((len(monos), len(polys) + len(monos)))
        for c, p in enumerate(polys):
            for m, v in zip(p.monoms(), p.coeffs()): A[idx[m], c] = float(v)
        for t in range(len(monos)): A[t, len(polys) + t] = 1.0
        bvec = np.zeros(len(monos))
        for m, v in zip(Pt.monoms(), Pt.coeffs()): bvec[idx[m]] = float(v)
        res = linprog(np.zeros(A.shape[1]), A_eq=A, b_eq=bvec, bounds=[(0, None)] * A.shape[1], method='highs')
        print(f'a={a} k={k}: certificate {"found" if res.status == 0 else "NOT found"}', flush=True)
