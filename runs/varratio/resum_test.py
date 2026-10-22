"""Cheap structural test of the Theorem 8.9 resummation for other ratios: build the move operators of the
Theorem 8.6 recurrence on Omega = {l + a <= N} (each move divided by c at its destination), P/Q (B-moves, even/odd j),
C+/C- (C-moves), U (straight), Afull = sum_j (-1)^j A_j, then G = (I - P/2)^{-1} and M = G(U + P^2/4 - Q + C+ - C- + Afull)G.
Reports min entry of M (exact) and whether (P) holds (terminal row). Usage: resum_test.py Ns families profiles rs lams"""
import sys, math, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from nonlinear_probe import profile, gfun, kappa_max
from rowN_probe import rowN

def mmul(X, Y, K):
    Z = [[F(0)] * K for _ in range(K)]
    for i in range(K):
        Xi = X[i]; Zi = Z[i]
        for k in range(K):
            x = Xi[k]
            if x:
                Yk = Y[k]
                for j in range(K):
                    if Yk[j]: Zi[j] += x * Yk[j]
    return Z

def Mmin(a_, b, c):
    N = len(c) - 1
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    nodes = [(l, a) for l in range(N + 1) for a in range(N + 1 - l)]
    idx = {nd: i for i, nd in enumerate(nodes)}; K = len(nodes)
    Z = lambda: [[F(0)] * K for _ in range(K)]
    W = lambda x, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * dif(x, n, l) for n in range(p, a + 1))
    U, P, Q, Cp, Cm, A = Z(), Z(), Z(), Z(), Z(), Z()
    for (l, a) in nodes:
        x = idx[(l, a)]
        if l + 1 + a <= N: U[idx[(l + 1, a)]][x] += a_[l + a] / c[l + 1]
        for j in range(N + 1):
            sg = 1 if j % 2 == 0 else -1
            lt, at = l + j + 1, a - 2 * j - 1
            if at >= 0 and lt + at <= N: A[idx[(lt, at)]][x] += sg * W(b, 2 * j + 1, j, l, a) / c[lt]
            lt, at = l + j + 1, a - 2 * j - 2
            if at >= 0 and lt + at <= N:
                (P if sg > 0 else Q)[idx[(lt, at)]][x] += W(c, 2 * j + 2, j, l, a) / c[lt]
            lt, at = l + j + 2, a - 2 * j - 2
            if at >= 0 and lt + at <= N:
                (Cp if sg > 0 else Cm)[idx[(lt, at)]][x] += (W(c, 2 * j + 2, j + 1, l, a) + W(b, 2 * j + 2, j + 1, l, a)) / c[lt]
    X = [[v / 2 for v in row] for row in P]
    G = [[F(int(i == j)) for j in range(K)] for i in range(K)]; Xm = [row[:] for row in G]
    for _ in range(N):
        Xm = mmul(Xm, X, K)
        G = [[g + y for g, y in zip(gr, yr)] for gr, yr in zip(G, Xm)]
    PP = mmul(P, P, K)
    S = [[U[i][j] + PP[i][j] / 4 - Q[i][j] + Cp[i][j] - Cm[i][j] + A[i][j] for j in range(K)] for i in range(K)]
    M = mmul(mmul(G, S, K), G, K)
    mn = min((M[i][j], nodes[i], nodes[j]) for i in range(K) for j in range(K))
    return mn

if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; fams = sys.argv[2].split(',')
    qs = [x if x[0] in 'pc' else F(x) for x in sys.argv[3].split(',')]; rs = [F(x) for x in sys.argv[4].split(',')]
    lams = [F(x) for x in sys.argv[5].split(',')]; t0 = time.time()
    for N in Ns:
        for q in qs:
            d = profile(N, q)
            for name in fams:
                g = gfun(name, N)
                for r in rs:
                    km = kappa_max(d, g, r)
                    for lam in lams:
                        k = km * lam
                        c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                        b = [dn - cn for dn, cn in zip(d, c)]; a = [1 - dn for dn in d]
                        mn = Mmin(a, b, c); row = rowN(a, b, c)
                        print(f"N={N} q={q} {name} r={r} lam={lam} minM={float(mn[0]):.3e} at {mn[1]}<-{mn[2]} rowmin={float(row[2]):.2e} [{time.time()-t0:.0f}s]", flush=True)
