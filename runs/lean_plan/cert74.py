"""Certificates with moves for a bilinear form F(l; u) = sum c_ij(l) u_i u_j that is >= 0 on log-concave u with
u_0 <= lam(l) u_1 (lam(l) = l, or l + 1): F is a combination of LC transfers u_{a+1}u_{b-1} - u_a u_b (a+2 <= b),
moves u_j (lam u_1 - u_0) and monomials u_a u_b with multipliers rational in l.
move_cert(F, lam, M) returns (L0, Q, terms, small):
  * for l = L0 + k: Q(k) * F = sum P_i(k) * g_i with Q and every P_i polynomials in k with nonnegative coefficients
    and Q(0) > 0 (terms = [(P_i, g_i)]);
  * for each l < L0: small[l] = [(rational c_i >= 0, g_i)] with F(l) = sum c_i g_i exactly.
A generator g is ('T', a, b), ('Z', j) or ('M', a, b). Planning helper for gen_cubicB.py (7/4 version)."""
import os, sys
import numpy as np, sympy as sp
from fractions import Fraction as Fr
from scipy.optimize import linprog
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'varratio'))
from key_cert_exact import certify

L, K = sp.symbols('l k', nonnegative=True)

def generators(M):
    G = []
    for a in range(0, M + 1):
        for b in range(a + 2, M + 1): G.append(('T', a, b))
    for j in range(0, M + 1): G.append(('Z', j))
    for a in range(0, M + 1):
        for b in range(a, M + 1): G.append(('M', a, b))
    return G

def gvec(g, lam):
    if g[0] == 'T':
        _, a, b = g; return {(a + 1, b - 1): sp.Integer(1), (a, b): sp.Integer(-1)}
    if g[0] == 'Z':
        _, j = g; out = {}
        k1 = tuple(sorted((1, j))); k0 = tuple(sorted((0, j)))
        out[k1] = out.get(k1, 0) + lam; out[k0] = out.get(k0, 0) - 1
        return out
    _, a, b = g; return {(a, b): sp.Integer(1)}

def _support(F, G, lam, lv):
    keys = sorted(set(k for g in G for k in gvec(g, lam)) | set(F)); ki = {k: i for i, k in enumerate(keys)}
    A = np.zeros((len(keys), len(G)))
    for c, g in enumerate(G):
        for k, v in gvec(g, lam).items(): A[ki[k], c] += float(sp.sympify(v).subs(L, lv))
    b = np.zeros(len(keys))
    for k, v in F.items(): b[ki[k]] += float(sp.sympify(v).subs(L, lv))
    res = linprog(np.zeros(len(G)), A_eq=A, b_eq=b, bounds=[(0, None)] * len(G), method='highs-ds')
    assert res.status == 0, ('LP infeasible', lv)
    return keys, [c for c in range(len(G)) if res.x[c] > 1e-9]

def _exact(F, G, lam, lv):
    keys = sorted(set(k for g in G for k in gvec(g, lam)) | set(F)); ki = {k: i for i, k in enumerate(keys)}
    A = [[Fr(0)] * len(G) for _ in keys]
    for c, g in enumerate(G):
        for k, v in gvec(g, lam).items():
            val = sp.Rational(sp.sympify(v).subs(L, lv)); A[ki[k]][c] += Fr(int(val.p), int(val.q))
    bv = [Fr(0)] * len(keys)
    for k, v in F.items():
        val = sp.Rational(sp.sympify(v).subs(L, lv)); bv[ki[k]] += Fr(int(val.p), int(val.q))
    verdict, x = certify(A, bv)
    assert verdict == 'CERTIFIED', (verdict, lv)
    return [(sp.Rational(x[c].numerator, x[c].denominator), G[c]) for c in range(len(G)) if x[c] != 0]

def move_cert(F, lam, M, lbig=1000):
    G = generators(M)
    keys, S = _support(F, G, lam, lbig)
    xs = sp.symbols(f'x0:{len(S)}')
    eqs = [sp.Eq(sum(xs[i] * gvec(G[c], lam).get(k, 0) for i, c in enumerate(S)), F.get(k, 0)) for k in keys]
    sol = sp.solve(eqs, xs, dict=True)
    assert sol and all(x in sol[0] for x in xs), 'support system not uniquely solvable'
    vals = [sp.together(sol[0][x]) for x in xs]
    Q = sp.Integer(1)
    for v in vals: Q = sp.lcm(Q, sp.fraction(v)[1])
    Q = sp.expand(Q)
    Ps = [sp.expand(sp.cancel(v * Q)) for v in vals]
    # verify the identity
    tot = {}
    for P, c in zip(Ps, S):
        for k, v in gvec(G[c], lam).items(): tot[k] = sp.expand(tot.get(k, 0) + P * v)
    for k in set(tot) | set(F): assert sp.expand(tot.get(k, 0) - Q * F.get(k, 0)) == 0, k
    def nonneg_after(L0):
        for poly in [Q] + Ps:
            pk = sp.Poly(sp.expand(poly.subs(L, L0 + K)), K)
            if any(c < 0 for c in pk.coeffs()): return False
        return sp.Poly(sp.expand(Q.subs(L, L0 + K)), K).eval(0) > 0
    L0 = next(L0 for L0 in range(0, 40) if nonneg_after(L0))
    if sp.Poly(sp.expand(Q.subs(L, L0 + K)), K).coeffs()[-1] < 0: Q, Ps = -Q, [-P for P in Ps]
    terms = [(sp.expand(P.subs(L, L0 + K)), G[c]) for P, c in zip(Ps, S) if P != 0]
    small = {lv: _exact(F, G, lam, lv) for lv in range(0, L0)}
    return L0, sp.expand(Q.subs(L, L0 + K)), terms, small
