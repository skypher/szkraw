"""For cubic ratios with r sig = u t tau: build the move operators of the b-part split psi = h - v - w - x
(each W_{2j+1,j} divided by c at the destination, signed (-1)^j as in A) and report min entries of
G X G, G (X + V) G, G (X + V + W) G, where G = (I - P/2)^{-1}. Usage: cubic_xblock.py Ns per us seed"""
import sys, math, random, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq
from resum_test import mmul

def blocks(d, r, t, tau, sig):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    D1 = lambda x: t + tau * x + sig * math.comb(x, 2); D2 = lambda x: tau + sig * x
    c = [rho(i) * d[i] for i in range(N + 1)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    f = lambda n, l: dif(d, n, l)
    parts = {'h': lambda n, l: (1 - rho(l + n)) * f(n, l), 'v': lambda n, l: n * D1(l + n - 1) * f(n - 1, l),
             'w': lambda n, l: math.comb(n, 2) * D2(l + n - 2) * f(n - 2, l) if n >= 2 else F(0),
             'x': lambda n, l: math.comb(n, 3) * sig * f(n - 3, l) if n >= 3 else F(0)}
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    nodes = [(l, a) for l in range(N + 1) for a in range(N + 1 - l)]
    idx = {nd: i for i, nd in enumerate(nodes)}; K = len(nodes)
    Z = lambda: [[F(0)] * K for _ in range(K)]
    P = Z(); Bk = {k: Z() for k in 'vwx'}
    for (l, a) in nodes:
        s = idx[(l, a)]
        for j in range(N + 1):
            lt, at = l + j + 1, a - 2 * j - 2
            if j % 2 == 0 and at >= 0 and lt + at <= N: P[idx[(lt, at)]][s] += W(lambda n, ll: dif(c, n, ll), 2 * j + 2, j, l, a) / c[lt]
            lt, at = l + j + 1, a - 2 * j - 1
            if j >= 1 and at >= 0 and lt + at <= N:
                for k in 'vwx':  # (-1)^j A_j contains -(-1)^j (V_j + W_j + X_j)
                    Bk[k][idx[(lt, at)]][s] += -(-1) ** j * W(parts[k], 2 * j + 1, j, l, a) / c[lt]
    X = [[v / 2 for v in row] for row in P]
    G = [[F(int(i == j)) for j in range(K)] for i in range(K)]; Xm = [row[:] for row in G]
    for _ in range(N):
        Xm = mmul(Xm, X, K); G = [[g + y for g, y in zip(gr, yr)] for gr, yr in zip(G, Xm)]
    sand = lambda Y: mmul(mmul(G, Y, K), G, K)
    add = lambda *Ys: [[sum(Y[i][j] for Y in Ys) for j in range(K)] for i in range(K)]
    out = {}
    for name, Y in (('X', Bk['x']), ('X+V', add(Bk['x'], Bk['v'])), ('X+V+W', add(Bk['x'], Bk['v'], Bk['w']))):
        S = sand(Y); out[name] = min((S[i][j], nodes[i], nodes[j]) for i in range(K) for j in range(K))
    return out

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); us = [F(z) for z in sys.argv[3].split(',')]
    rng = random.Random(int(sys.argv[4])); worst = {}
    for u in us:
        for N in Ns:
            for _ in range(per):
                sg = lc_seq(rng, N)
                Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
                d = [z / Dd[N] for z in Dd]
                r = min(F(rng.choice([1, 2, 5, 10, 16, 19])) / 20, F(19, 20))
                t1, tau1 = F(rng.choice([1, 1, 2, 5])), F(rng.choice([1, 1, 3, 10]))
                def mk(lam): return lam * t1, lam * tau1, u * lam * t1 * lam * tau1 / r
                def okb(lam):
                    t, tau, sig = mk(lam); rh = lambda z: r + t * z + tau * math.comb(z, 2) + sig * math.comb(z, 3)
                    bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
                    return rh(N) <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
                lo, hi = F(0), F(1)
                while okb(hi): hi *= 2
                for _ in range(30):
                    mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
                out = blocks(d, r, *mk(lo))
                for k, v in out.items():
                    if k not in worst or v[0] < worst[k][0]: worst[k] = (v[0], v[1], v[2], u, N, r)
            print(f"[{time.strftime('%H:%M:%S')}] u={u} N={N} done; worst so far " + ', '.join(f"{k}={float(v[0]):.3e}" for k, v in worst.items()), flush=True)
