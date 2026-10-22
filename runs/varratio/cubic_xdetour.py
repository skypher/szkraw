"""Two-sided detour test for the cubic X moves: X_+ = X_1 + X_3 + ..., X_- = X_2 + X_4 + ... (operators on Omega,
each divided by c at the destination), P = sum of B_j with j even. Reports min over entries with X_- > 0 of
(X_+ P + P X_+) / X_-  (needs >= 4), and of X_+ P / X_-, P X_+ / X_- separately (operator products: P X_+ = X_+ first).
Usage: cubic_xdetour.py Ns per us seed [parts, e.g. vwx]"""
import sys, math, random, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq
from resum_test import mmul

PARTS = 'x'

def ops(d, r, t, tau, sig):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    D1 = lambda x: t + tau * x + sig * math.comb(x, 2); D2 = lambda x: tau + sig * x
    c = [rho(i) * d[i] for i in range(N + 1)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    f = lambda n, l: dif(d, n, l)
    pv = lambda n, l: n * D1(l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
    pw = lambda n, l: math.comb(n, 2) * D2(l + n - 2) * f(n - 2, l) if n >= 2 else F(0)
    px = lambda n, l: math.comb(n, 3) * sig * f(n - 3, l) if n >= 3 else F(0)
    sel = {'v': pv, 'w': pw, 'x': px}
    xpart = lambda n, l: sum(sel[k](n, l) for k in PARTS)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    nodes = [(l, a) for l in range(N + 1) for a in range(N + 1 - l)]
    idx = {nd: i for i, nd in enumerate(nodes)}; K = len(nodes)
    Z = lambda: [[F(0)] * K for _ in range(K)]
    P, Xp, Xm = Z(), Z(), Z()
    for (l, a) in nodes:
        s = idx[(l, a)]
        for j in range(N + 1):
            lt, at = l + j + 1, a - 2 * j - 2
            if j % 2 == 0 and at >= 0 and lt + at <= N: P[idx[(lt, at)]][s] += W(lambda n, ll: dif(c, n, ll), 2 * j + 2, j, l, a) / c[lt]
            lt, at = l + j + 1, a - 2 * j - 1
            if j >= 1 and at >= 0 and lt + at <= N:
                (Xp if j % 2 == 1 else Xm)[idx[(lt, at)]][s] += W(xpart, 2 * j + 1, j, l, a) / c[lt]
    return nodes, P, Xp, Xm, K

def ratios(d, r, t, tau, sig):
    nodes, P, Xp, Xm, K = ops(d, r, t, tau, sig)
    XP = mmul(Xp, P, K); PX = mmul(P, Xp, K)  # XP: P first, then X_+ ; PX: X_+ first, then P
    best = {'two': None, 'Pfirst': None, 'Xfirst': None}
    for i in range(K):
        for j in range(K):
            if Xm[i][j] > 0:
                for k, v in (('two', XP[i][j] + PX[i][j]), ('Pfirst', XP[i][j]), ('Xfirst', PX[i][j])):
                    q = v / Xm[i][j]
                    if best[k] is None or q < best[k][0]: best[k] = (q, nodes[i], nodes[j])
    return best

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); us = [F(z) for z in sys.argv[3].split(',')]
    rng = random.Random(int(sys.argv[4]))
    if len(sys.argv) > 5: PARTS = sys.argv[5]
    for u in us:
        worst = {}
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
                b = ratios(d, r, *mk(lo))
                for k, v in b.items():
                    if v and (k not in worst or v[0] < worst[k][0]): worst[k] = v + (N, r)
            print(f"[{time.strftime('%H:%M:%S')}] u={u} N={N}: " + ', '.join(f"{k}={float(v[0]):.4g}@{v[1]}<-{v[2]}" for k, v in worst.items()), flush=True)
