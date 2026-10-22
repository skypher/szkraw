"""Independent exact check of the round-3 consult's quadratic-family proof (reviews/consult-E-answer.md).
Profile D_i = i + x C(i,2), T = D_N, h = x/2, (u,v) = (t,1). Checks, as polynomials in t at rational x:
 (a) kernel recurrence (1) with c_{0,a} = [a = k] reproduces L_{mn}^k = H_{mn}^k e_m e_n / e_k via K_k = sum c_{r,a} S^a Z^r;
 (b) support invariant c_{r,a} = 0 for r + a > N, and A_r c_{r,a} has nonnegative coefficients in t;
 (c) D_{mn}^k = e_k/(T e_m e_n) W_{mn}^k and W_k = (w - z) B_k with B_k = {T - D(E)} K_k + h Z (K_k)_SS;
 (d) closed terminal formulas (9) and (10)."""
import sys
from fractions import Fraction as F
from math import comb, factorial
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables, padd, psc, ptm

def pe(p, q): n = max(len(p), len(q)); return all((p[i] if i < len(p) else 0) == (q[i] if i < len(q) else 0) for i in range(n))
def pmul(p, q):
    if not p or not q: return []
    out = [F(0)]*(len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): out[i+j] += x*y
    return out

def run(N, x):
    D = [i + x*comb(i, 2) for i in range(N+1)]; T = D[N]; h = x/2
    Dfun = lambda s: s + h*s*(s-1)
    d = [Di/T for Di in D]
    H, Dt = tables(d)
    A = [F(1)]
    for j in range(1, N+1): A.append(A[-1]*D[j])
    Q = [F(1)]
    for j in range(N): Q.append(Q[-1]*(T - D[j]))
    e = [Q[r]/A[r] for r in range(N+1)]
    bad = {'a': 0, 'b': 0, 'c': 0}; nH = nD = 0
    for k in range(N+1):
        # kernel coefficients c[r][a] as t-polynomials
        R = N + 2
        c = {(r, a): [] for r in range(-1, R) for a in range(0, 2*R + 3)}
        c[(0, k)] = [F(1)]
        for r in range(0, R - 1):
            for a in range(0, 2*R):
                v = psc(c[(r, a)], T - Dfun(r + a))
                v = padd(v, psc(ptm(c.get((r, a+1), [])), (a+1)*(1 + h*(a + 2*r))))
                v = padd(v, psc(padd(c.get((r, a+2), []), c.get((r-1, a+2), [])), h*(a+1)*(a+2)))
                c[(r+1, a)] = psc(v, 1/D[r+1]) if r + 1 <= N else psc(v, F(0))
        # (b) support and positivity of A_r c
        for (r, a), p in c.items():
            if r < 0 or not any(p): continue
            if r + a > N: bad['b'] += 1
            if r <= N and any(co < 0 for co in psc(p, A[r])): bad['b'] += 1
        # K_k(z,w) coefficients: [z^m w^n] sum c_{r,a} (z+w)^a (zw)^r = sum_r c_{r,a} C(a, m-r) with a = m+n-2r
        def L(m, n):
            out = []
            for r in range(0, min(m, n) + 1):
                a = m + n - 2*r
                if (r, a) in c and any(c[(r, a)]): out = padd(out, psc(c[(r, a)], comb(a, m - r)))
            return out
        for m in range(N+1):
            for n in range(N+1):
                Lh = psc(H[m][n][k], e[m]*e[n]/e[k]); nH += 1
                if not pe(L(m, n), Lh): bad['a'] += 1
        # (c) B_k and the D identity
        def B(m, n):     # [z^m w^n] of (w - z) B_k
            def Bcoef(r, a):    # coefficient of S^a Z^r in B_k
                out = psc(c.get((r, a), []), T - Dfun(a + r))
                if r >= 1: out = padd(out, psc(c.get((r-1, a+2), []), h*(a+2)*(a+1)))
                return out
            out = []
            for r in range(0, min(m, n) + 1):
                a = m + n - 1 - 2*r
                if a < 0: continue
                co = comb(a, m - r) - (comb(a, m - r - 1) if m - r - 1 >= 0 else 0)
                out = padd(out, psc(Bcoef(r, a), co))
            return out
        for m in range(1, N+1):
            for n in range(m+1, N+1):
                W = padd(psc(L(m, n-1), T - D[n-1]), psc(L(m-1, n), -(T - D[m-1])))
                if not pe(W, B(m, n)): bad['c'] += 1
                Dmn = padd(psc(H[m][n-1][k], d[n]), psc(H[m-1][n][k], -d[m]))
                if not pe(Dmn, psc(W, e[k]/(T*e[m]*e[n]))): bad['c'] += 1
                nD += 1
    # (d) terminal formulas
    Bp = N - 1 + 2/x
    def rising(b, j):
        out = F(1)
        for i in range(j): out *= (b + i)
        return out
    badd = 0
    for m in range(0, N+1):
        f9 = [F(0)]*(m+1)
        for j in range(m//2 + 1): f9[m - 2*j] = F(factorial(m), factorial(j)*factorial(m - 2*j))/rising(Bp, j) if j else F(1)
        if j == 0: pass
        f9 = [F(0)]*(m+1)
        for j in range(m//2 + 1): f9[m - 2*j] = F(factorial(m), factorial(j)*factorial(m - 2*j))/rising(Bp + m - j, j)
        if not pe(f9, H[m][N][N]): badd += 1
    for m in range(1, N):
        a_m = (T - D[m])/T
        f10 = [F(0)]*(m+1)
        for j in range(1, (m+1)//2 + 1):
            f10[m + 1 - 2*j] = a_m*factorial(m)*(2*Bp + m - 1)/(factorial(j-1)*factorial(m + 1 - 2*j)*rising(Bp + m - j, j + 1))
        if not pe(f10, Dt[(m, N, N)]): badd += 1
    return nH, nD, bad, badd

if __name__ == '__main__':
    for N in (3, 4, 5, 6, 8, 10):
        for x in (F(1, 3), F(1), F(7, 2)):
            nH, nD, bad, badd = run(N, x)
            print(f'N={N} x={x}: {nH} H identities, {nD} D identities; failures {bad}; terminal formula failures {badd}', flush=True)
