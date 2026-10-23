"""Exact certificates that every coefficient l_k(u) of Lin(P) is >= 0 for all LC u (quadratic in u), generators
u_{i+1}u_{j-1} - u_i u_j (i+1 <= j-1) and products u_i u_j. Usage: key_lin_cert.py amax"""
import sys, itertools
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
from key_cert_exact import certify
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1))
    P, Lin, Quad, f1, Dc = parts(list(U) + [sp.Integer(0)] * 3, a)
    co = sp.Poly(Lin, *P); verdicts = {}
    for k in range(a + 1):
        S = sp.expand(co.coeff_monomial(P[k]))
        if S == 0: verdicts['zero'] = verdicts.get('zero', 0) + 1; continue
        gens = [sp.expand(U[i + 1] * U[j - 1] - U[i] * U[j]) for i in range(a + 1) for j in range(i + 2, a + 1)]
        gens += [U[i] * U[j] for i, j in itertools.combinations_with_replacement(range(a + 1), 2)]
        polys = [sp.Poly(g, *U) for g in gens]; Ps = sp.Poly(S, *U)
        monos = sorted(set(m for p in polys + [Ps] for m in p.monoms())); idx = {m: t for t, m in enumerate(monos)}
        A = [[Fr(0)] * len(polys) for _ in monos]
        for col, p in enumerate(polys):
            for m, v in zip(p.monoms(), p.coeffs()): A[idx[m]][col] = Fr(int(v))
        bv = [Fr(0)] * len(monos)
        for m, v in zip(Ps.monoms(), Ps.coeffs()): bv[idx[m]] = Fr(int(sp.numer(v)), int(sp.denom(v)))
        v = certify(A, bv)[0]; verdicts[v] = verdicts.get(v, 0) + 1
    print(f'a={a}: Lin coefficients {verdicts}', flush=True)
