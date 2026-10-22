"""Recover the symmetric-kernel coefficients c_{r,a} (K_k = sum c S^a Z^r) from the true L_{mn}^k = H e_m e_n / e_k for a
given profile, and report the minimum coefficient (over t-powers, k, r, a) scaled by A_r: is the (S, Z) kernel positive?"""
import sys, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables, padd, psc
def kernel_min(sig, N):
    D = [sum(comb(i, j)*sig[j-1] for j in range(1, min(i, len(sig)) + 1)) for i in range(N+1)]; T = D[N]
    d = [x/T for x in D]; H, _ = tables(d)
    A = [F(1)]
    for j in range(1, N+1): A.append(A[-1]*D[j])
    Q = [F(1)]
    for j in range(N): Q.append(Q[-1]*(T - D[j]))
    e = [Q[r]/A[r] for r in range(N+1)]
    worst = F(0); where = None
    for k in range(N+1):
        L = lambda m, n: psc(H[m][n][k], e[m]*e[n]/e[k])
        c = {}
        # solve L_{m,n} = sum_r c_{r, m+n-2r} C(m+n-2r, m-r) for m <= n, in increasing m (r = m term is c_{m, n-m})
        for m in range(N+1):
            for n in range(m, N+1):
                rest = L(m, n)
                for r in range(m):
                    a = m + n - 2*r
                    rest = padd(rest, psc(c.get((r, a), []), -comb(a, m - r)))
                c[(m, n - m)] = rest           # coefficient C(n-m, 0) = 1
        for (r, a), p in c.items():
            for co in p:
                v = co*A[r]
                if v < worst: worst = v; where = (k, r, a)
    return worst, where
if __name__ == '__main__':
    for N in (4, 5, 6, 8):
        for x in (F(1, 2), F(2)):
            for theta in (F(0), F(1, 2), F(1), F(3, 2), F(3)):
                sig = [F(1), x, theta*x*x]
                wv, wh = kernel_min(sig, N)
                print(f'N={N} sigma=(1,{x},{theta}*x^2) [{"LC" if theta <= 1 else "not LC"}]: min A_r c = {float(wv):.3e} at (k,r,a)={wh}', flush=True)
