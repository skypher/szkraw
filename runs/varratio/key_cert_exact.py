"""Exact certification of degree-2 key certificates. Builds the generator matrix in exact rationals, gets a basic
solution from HiGHS (dual simplex) on a row/column-rescaled float copy, then re-solves the system restricted to the
support EXACTLY (rational Gaussian elimination) and accepts only if the exact solution is >= 0 and reproduces the key.
Usage: key_cert_exact.py a (rand seed | geo w) [nolc]"""
import sys, random, math
from fractions import Fraction as Fr
import sympy as sp
import numpy as np
from scipy.optimize import linprog
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_cert_lp import key_poly, lc_u

def build(u, a, use_lc):
    key, P, b = key_poly(u, a); Pv = P[:a + 1]
    gens = []
    for m in range(a):
        g = sp.expand(b(m + 1) - b(m))
        for k in range(a + 1): gens.append(sp.expand(g * Pv[k]))
    for m in range(a + 1):
        for k in range(a + 1): gens.append(sp.expand(b(m) * Pv[k]))
    for k in range(a + 1): gens.append(Pv[k])
    for i in range(a + 1):
        for j in range(i, a + 1): gens.append(Pv[i] * Pv[j])
    if use_lc:
        for i in range(1, a + 1):
            for j in range(i, a): gens.append(sp.expand(Pv[i] * Pv[j] - Pv[i - 1] * Pv[j + 1]))
    polys = [sp.Poly(g, *Pv) for g in gens]; Pk = sp.Poly(key, *Pv)
    monos = sorted(set(m for p in polys + [Pk] for m in p.monoms())); idx = {m: t for t, m in enumerate(monos)}
    A = [[Fr(0)] * len(polys) for _ in monos]
    for col, p in enumerate(polys):
        for m, v in zip(p.monoms(), p.coeffs()): A[idx[m]][col] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    bv = [Fr(0)] * len(monos)
    for m, v in zip(Pk.monoms(), Pk.coeffs()): bv[idx[m]] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    return A, bv

def exact_solve(A, bv, cols):
    # solve A[:, cols] x = bv exactly; return x (dict) or None if inconsistent
    m, n = len(A), len(cols)
    M = [[A[i][c] for c in cols] + [bv[i]] for i in range(m)]
    piv = []; r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if M[i][c] != 0), None)
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        inv = 1 / M[r][c]; M[r] = [x * inv for x in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == m: break
    if any(all(M[i][c] == 0 for c in range(n)) and M[i][n] != 0 for i in range(m)): return None
    x = {cols[c]: Fr(0) for c in range(n)}
    for i, c in enumerate(piv): x[cols[c]] = M[i][n]
    return x

def certify(A, bv):
    m, n = len(A), len(A[0])
    Af = np.array([[float(x) for x in row] for row in A]); bf = np.array([float(x) for x in bv])
    rs = np.array([max(abs(Af[i]).max(), abs(bf[i]), 1e-300) for i in range(m)])
    Af = Af / rs[:, None]; bf = bf / rs
    cs = np.array([max(abs(Af[:, j]).max(), 1e-300) for j in range(n)]); Af = Af / cs[None, :]
    res = linprog(np.zeros(n), A_eq=Af, b_eq=bf, bounds=[(0, None)] * n, method='highs-ds')
    if res.status != 0: return 'float-infeasible', None
    sup = [j for j in range(n) if res.x[j] > 1e-12]
    x = exact_solve(A, bv, sup)
    if x is None: return 'support-inconsistent', None
    if any(v < 0 for v in x.values()): return 'exact-negative', None
    full = [x.get(j, Fr(0)) for j in range(n)]
    ok = all(sum(A[i][j] * full[j] for j in range(n)) == bv[i] for i in range(m))
    return ('CERTIFIED' if ok else 'mismatch'), full

if __name__ == '__main__':
    a = int(sys.argv[1]); use_lc = 'nolc' not in sys.argv
    if sys.argv[2] == 'rand': u = lc_u(random.Random(int(sys.argv[3])), a + 3); kind = f'rand seed {sys.argv[3]}'
    else:
        w = sp.Rational(sys.argv[3]); u = [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]; kind = f'geo w={w}'
    A, bv = build(u, a, use_lc)
    verdict, _ = certify(A, bv)
    print(f'a={a} {kind} {"with" if use_lc else "without"} LC: {verdict}', flush=True)
