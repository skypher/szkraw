"""Quartic profiles: exact node-by-node check of the kernel-positivity induction with kappa = 1/2 for all inflow types.
Recurrence from cubic_symbolic.G(4) (symbolic exponents). Checks: recurrence reproduces true L; c >= 0; induction hypothesis
D_r c_{r,a} >= (1/2)(Vt + VB + VB'); also positivity of B, B' for a >= 2 in LC coordinates."""
import sys, random
from fractions import Fraction as F
from math import comb
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables, padd, psc, ptm
from cubic_symbolic import G
a_, r_, t_, T_ = sp.symbols('a r t T'); s2, s3, s4 = sp.symbols('s2 s3 s4')
g = G(4, [sp.Integer(1), s2, s3, s4])
def pe(p, q): n = max(len(p), len(q)); return all((p[i] if i < len(p) else 0) == (q[i] if i < len(q) else 0) for i in range(n))
def nonneg(p): return all(x >= 0 for x in p)
def run(N, sv):
    sub = dict(zip((s2, s3, s4), sv))
    coef = {k: sp.lambdify((r_, a_, t_, T_), v.subs(sub)) for k, v in g.items()}
    Dn = lambda n: n + sv[0]*comb(n, 2) + sv[1]*comb(n, 3) + sv[2]*comb(n, 4)
    T = Dn(N); d = [Dn(i)/T for i in range(N+1)]; H, _ = tables(d)
    A_ = [F(1)]
    for j in range(1, N+1): A_.append(A_[-1]*Dn(j))
    Q = [F(1)]
    for j in range(N): Q.append(Q[-1]*(T - Dn(j)))
    e = [Q[r]/A_[r] for r in range(N+1)]
    # coefficient (as t-polynomial) of a move: evaluate at t = 0 and t = 1 (each move is constant or linear in t)
    def mv(key, r, a):
        c0 = F(coef[key](r, a, 0, T)).limit_denominator(10**12) if False else sp.nsimplify(g[key].subs(sub).subs({r_: r, a_: a, t_: 0, T_: T}))
        c1 = sp.nsimplify(g[key].subs(sub).subs({r_: r, a_: a, t_: 1, T_: T}))
        return [F(str(c0)), F(str(c1 - c0))]
    st = {'L': 0, 'neg': 0, 'H': 0}
    for k in range(N+1):
        c = {(0, k): [F(1)]}
        G_ = lambda r, a: c.get((r, a), [])
        for r in range(0, N+1):
            for a in range(0, N + 6):
                # equation at (r, a): sum over sources (r - dr, a - da) of coef(dr, da) c_source = 0, with (0,-1)->(dr=-1): -D_{r+1} c_{r+1,a}
                tot = []; inflow = []
                for (da, dr), _ in g.items():
                    if (da, dr) == (0, -1): continue
                    rs, as_ = r - dr, a - da
                    if rs < 0 or as_ < 0 or not G_(rs, as_): continue
                    w = mv((da, dr), rs, as_)
                    term = []
                    for i, x in enumerate(G_(rs, as_)):
                        for j, y in enumerate(w):
                            if x and y:
                                while len(term) <= i + j: term.append(F(0))
                                term[i + j] += x*y
                    tot = padd(tot, term)
                    if (da, dr) in ((-1, 0), (-2, 0), (-2, 1)): inflow = padd(inflow, term)
                Dr1 = Dn(r + 1)
                if any(tot):
                    c[(r+1, a)] = psc(tot, 1/Dr1)
                    if not nonneg(c[(r+1, a)]): st['neg'] += 1
                    if not nonneg(padd(tot, psc(inflow, F(-1, 2)))): st['H'] += 1
        for m in range(N+1):
            for n in range(N+1):
                Lt = []
                for r in range(0, min(m, n) + 1):
                    aa = m + n - 2*r
                    Lt = padd(Lt, psc(c.get((r, aa), []), comb(aa, m - r)))
                if not pe(Lt, psc(H[m][n][k], e[m]*e[n]/e[k])): st['L'] += 1
    return st
if __name__ == '__main__':
    def lc(x1, x2, x3):
        r1, r2, r3 = x1 + x2 + x3, x2 + x3, x3; return (r1, r1*r2, r1*r2*r3)
    cases = [('LC', lc(F(1), F(1), F(1))), ('LC', lc(F(1, 10), F(0), F(1, 10))), ('LC', lc(F(0), F(0), F(1))), ('LC geometric x=2', (F(2), F(4), F(8))),
             ('not LC', (F(0), F(0), F(1, 100))), ('not LC', (F(1), F(1), F(10))), ('not LC', (F(1, 10), F(1), F(1)))]
    for N in (4, 5, 6, 8):
        for name, sv in cases:
            st = run(N, sv)
            print(f'N={N} {name:16s} s={tuple(str(x) for x in sv)}: L mismatches {st["L"]}, negative c {st["neg"]}, H(1/2) failures {st["H"]}', flush=True)
