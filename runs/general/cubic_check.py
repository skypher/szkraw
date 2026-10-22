"""Cubic profiles D_i = i + s2 C(i,2) + s3 C(i,3): exact check of the kernel-positivity proof.
(a) the closed-form kernel recurrence (cubic_forms.py) with c_{0,a} = [a = k] reproduces the true L_{mn}^k for all m, n, k;
(b) induction hypothesis H(r): c_{r,a} >= 0 and D_r c_{r,a} - (1/2)(t-inflow + B-inflow) >= 0 coefficientwise in t;
(c) the jump is dominated: (1/2)(t-inflow + B-inflow of node (r+1,a)) - J >= 0, as used in the proof."""
import sys, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables, padd, psc, ptm
def pe(p, q): n = max(len(p), len(q)); return all((p[i] if i < len(p) else 0) == (q[i] if i < len(q) else 0) for i in range(n))
def nonneg(p): return all(x >= 0 for x in p)

def run(N, s2, s3):
    Dn = lambda n: n + s2*comb(n, 2) + s3*comb(n, 3) if n >= 0 else F(0)
    T = Dn(N)
    Bf = lambda r, a: comb(a, 2)*(s2 + r*s3) + comb(a, 3)*s3
    Bp = lambda r, a: comb(a, 2)*(s2 + r*s3) + 2*comb(a, 3)*s3
    d = [Dn(i)/T for i in range(N+1)]; H, _ = tables(d)
    A = [F(1)]
    for j in range(1, N+1): A.append(A[-1]*Dn(j))
    Q = [F(1)]
    for j in range(N): Q.append(Q[-1]*(T - Dn(j)))
    e = [Q[r]/A[r] for r in range(N+1)]
    stats = {'L': 0, 'H': 0, 'J': 0, 'neg': 0}
    for k in range(N+1):
        amax = N + 4
        c = {(r, a): [] for r in range(-1, N+2) for a in range(0, amax + 4)}
        c[(0, k)] = [F(1)]
        for r in range(0, N+1):
            for a in range(0, amax):
                g = lambda rr, aa: c.get((rr, aa), [])
                U = padd(psc(g(r, a), T - Dn(r + a)), psc(g(r-1, a+2), Bp(r-1, a+2)))
                Vt = psc(ptm(g(r, a+1)), Dn(r + a + 1) - Dn(r))
                VB = psc(g(r, a+2), Bf(r, a+2))
                J = psc(ptm(g(r-1, a+3)), s3*comb(a+3, 3))
                tot = padd(padd(U, padd(Vt, VB)), psc(J, -1))
                c[(r+1, a)] = psc(tot, 1/Dn(r+1))
                # (b) at the new node: D_{r+1} c - (1/2)(Vt + VB) >= 0, and c >= 0
                if not nonneg(padd(tot, psc(padd(Vt, VB), F(-1, 2)))): stats['H'] += 1
                if not nonneg(c[(r+1, a)]): stats['neg'] += 1
                if not nonneg(padd(psc(padd(Vt, VB), F(1, 2)), psc(J, -1))): stats['J'] += 1
        for m in range(N+1):
            for n in range(N+1):
                Lt = []
                for r in range(0, min(m, n) + 1):
                    a = m + n - 2*r
                    Lt = padd(Lt, psc(c.get((r, a), []), comb(a, m - r)))
                if not pe(Lt, psc(H[m][n][k], e[m]*e[n]/e[k])): stats['L'] += 1
    return stats

if __name__ == '__main__':
    for N in (3, 4, 5, 6, 8, 10):
        for s2, s3 in ((F(0), F(1)), (F(1, 10), F(10)), (F(1), F(1)), (F(2), F(1, 3)), (F(0), F(100)), (F(5), F(0))):
            st = run(N, s2, s3)
            print(f'N={N} s2={s2} s3={s3} [{"LC" if s2*s2 >= s3 else "not LC"}]: L mismatches {st["L"]}, H(r) failures {st["H"]}, '
                  f'jump-domination failures {st["J"]}, negative c {st["neg"]}', flush=True)
