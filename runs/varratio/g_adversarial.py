"""Adversarial test of conjecture (G) in the regime where the binomial-ray key fails: geometric profiles with small
increment ratio w (d_i = ((1+w)^i - 1)/((1+w)^N - 1)), steep exponential ratios rho = r B^x (r = lam * max with b
nondecreasing), and moderately steep ones. Checks (P) via rows g(m,N;k) (N > 16) or full tables, and the full key
(gamma_V = 2, gamma_W = 0) at all sources. Usage: g_adversarial.py Ns ws Bs lams"""
import sys, math, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from rowN_probe import rowN

def run(N, w, B, lam, check_key):
    d = [((1 + w) ** i - 1) / ((1 + w) ** N - 1) for i in range(N + 1)]
    g = [B ** i for i in range(N + 1)]
    def ok(r):
        rho = [r * x for x in g]; b = [(1 - p) * dd for p, dd in zip(rho, d)]
        return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(N))
    lo, hi = F(0), 1 / g[-1]
    if ok(hi): lo = hi
    else:
        for _ in range(40):
            mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    r = lo * lam; rv = [r * x for x in g] + [r * B ** i for i in range(N + 1, 2 * N + 3)]
    c = [rv[i] * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
    if N <= 16: x = first_negative(linearization(a_, b, c)); P = (x is None, x)
    else: m, k, v = rowN(a_, b, c); P = (v >= 0, (m, N, k, float(v)))
    keymin = None
    if check_key:
        dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
        f = lambda n, l: dif(d, n, l); phi = lambda n, l: dif(c, n, l)
        h = lambda n, l: (1 - rv[l + n]) * f(n, l)
        v = lambda n, l: n * dif(rv, 1, l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
        W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
        for l in range(N):
            for a in range(3, N + 1 - l):
                lhs = (b[l + a] - b[l]) * W(phi, 2, 0, l + 1, a - 1) + W(phi, 2, 0, l, a) * (b[l + a - 1] - b[l + 1])
                rhs = c[l + 1] * (4 * W(h, 3, 1, l, a) - 2 * W(v, 3, 1, l, a))
                if rhs > 0:
                    q = lhs / rhs
                    if keymin is None or q < keymin[0]: keymin = (q, l, a)
    return P, keymin

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; ws = [F(z) for z in sys.argv[2].split(',')]
    Bs = [F(z) for z in sys.argv[3].split(',')]; lams = [F(z) for z in sys.argv[4].split(',')]
    for N in Ns:
        for w in ws:
            for B in Bs:
                for lam in lams:
                    t0 = time.time()
                    P, km = run(N, w, B, lam, N <= 22)
                    print(f'N={N} w={w} B={B} lam={lam}: (P) {"holds" if P[0] else "FAILS " + str(P[1])}; '
                          f'key min ratio {float(km[0]):.4g} at (l,a)={km[1:]}' if km else
                          f'N={N} w={w} B={B} lam={lam}: (P) {"holds" if P[0] else "FAILS " + str(P[1])}', f'[{time.time()-t0:.0f}s]', flush=True)
