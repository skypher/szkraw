"""Diagnose which part of the Theorem 8.11 resummation fails for cubic ratios rho(x) = r + t x + tau C(x,2) + sig C(x,3):
min entries of R = U + P^2/4 - Q, of G A G, of G (C+ - C-) G and of M = G (R + C + A) G, with sources/destinations.
Also the scalar B-detour 4 c_{l+1} B_1(l,a) <= B_0(l,a) B_0(l+1,a-2) at every source. Usage: cubic_diag.py N r t tau sig [q]"""
import sys, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from nonlinear_probe import profile
from resum_test import mmul

def run(N, r, t, tau, sig, q=F(1), d=None):
    d = profile(N, q) if d is None else d
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
    assert all(b[i + 1] >= b[i] for i in range(N)), 'b not nondecreasing'
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    nodes = [(l, a) for l in range(N + 1) for a in range(N + 1 - l)]
    idx = {nd: i for i, nd in enumerate(nodes)}; K = len(nodes)
    Z = lambda: [[F(0)] * K for _ in range(K)]
    W = lambda x, p, qq, l, a: sum(math.comb(n - p + qq, qq) * math.comb(a, n) * dif(x, n, l) for n in range(p, a + 1))
    U, P, Q, Cp, Cm, A = Z(), Z(), Z(), Z(), Z(), Z()
    det = []
    for (l, a) in nodes:
        x = idx[(l, a)]
        if l + 1 + a <= N: U[idx[(l + 1, a)]][x] += a_[l + a] / c[l + 1]
        if a >= 4 and l + 1 + a - 2 <= N and l + 1 <= N:
            lhs = W(c, 2, 0, l, a) * W(c, 2, 0, l + 1, a - 2); rhs = 4 * c[l + 1] * W(c, 4, 1, l, a)
            det.append((lhs - rhs, (l, a)))
        for j in range(N + 1):
            sg = 1 if j % 2 == 0 else -1
            lt, at = l + j + 1, a - 2 * j - 1
            if at >= 0 and lt + at <= N: A[idx[(lt, at)]][x] += sg * W(b, 2 * j + 1, j, l, a) / c[lt]
            lt, at = l + j + 1, a - 2 * j - 2
            if at >= 0 and lt + at <= N: (P if sg > 0 else Q)[idx[(lt, at)]][x] += W(c, 2 * j + 2, j, l, a) / c[lt]
            lt, at = l + j + 2, a - 2 * j - 2
            if at >= 0 and lt + at <= N:
                (Cp if sg > 0 else Cm)[idx[(lt, at)]][x] += (W(c, 2 * j + 2, j + 1, l, a) + W(b, 2 * j + 2, j + 1, l, a)) / c[lt]
    X = [[v / 2 for v in row] for row in P]
    G = [[F(int(i == j)) for j in range(K)] for i in range(K)]; Xm = [row[:] for row in G]
    for _ in range(N):
        Xm = mmul(Xm, X, K); G = [[g + y for g, y in zip(gr, yr)] for gr, yr in zip(G, Xm)]
    PP = mmul(P, P, K)
    R = [[U[i][j] + PP[i][j] / 4 - Q[i][j] for j in range(K)] for i in range(K)]
    C = [[Cp[i][j] - Cm[i][j] for j in range(K)] for i in range(K)]
    sand = lambda Y: mmul(mmul(G, Y, K), G, K)
    S = [[R[i][j] + C[i][j] + A[i][j] for j in range(K)] for i in range(K)]
    out = {}
    for name, Y in (('R', R), ('GAG', sand(A)), ('GCG', sand(C)), ('M', sand(S))):
        out[name] = min((Y[i][j], nodes[i], nodes[j]) for i in range(K) for j in range(K))
    out['Bdetour'] = min(det) if det else None
    return out

if __name__ == '__main__':
    N = int(sys.argv[1]); r, t, tau, sig = (F(x) for x in sys.argv[2:6]); q = F(sys.argv[6]) if len(sys.argv) > 6 else F(1)
    for k, v in run(N, r, t, tau, sig, q).items():
        print(k, float(v[0]), v[1:], flush=True)
