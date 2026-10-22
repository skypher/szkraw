"""Probe property (P) for nonlinear increasing ratios rho_n = c_n/d_n (exact arithmetic).
Families of g with rho_n = r + kappa*g(n): concave/convex kinks and quadratics. Profiles: linear d_n = n/N
and geometric increments q (log-concave Newton coefficients). kappa is a fraction lam of the largest value
on a grid keeping b nondecreasing and rho_N <= 1. Reports the first negative coefficient.
Usage: nonlinear_probe.py Nmax [Nmin] [families] [qs] [rs]"""
import sys, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw')
from probe import linearization, first_negative

def profile(N, q):
    if isinstance(q, str):  # polynomial profiles: 'p<k>' Newton (1, k/N); 'c<k>' Newton (1, k/N, (k/N)^2)
        al = F(int(q[1:]), N); be = al * al if q[0] == 'c' else F(0)
        from math import comb
        D = [n + al * comb(n, 2) + be * comb(n, 3) for n in range(N + 1)]
        return [x / D[N] for x in D]
    inc = [q ** i for i in range(N)]
    s = sum(inc)
    d = [F(0)]
    for x in inc:
        d.append(d[-1] + x / s)
    return d

def gfun(name, N):
    if name == 'lin': return [F(n, N) for n in range(N + 1)]
    if name == 'quad_convex': return [F(n * n, N * N) for n in range(N + 1)]
    if name == 'cubic_convex': return [F(n ** 3, N ** 3) for n in range(N + 1)]
    if name == 'exp_convex': return [F(2) ** n / F(2) ** N for n in range(N + 1)]
    if name == 'linquad': return [F(n, N) + F(n * n, N * N) for n in range(N + 1)]
    if name == 'quad_concave': return [F(2 * n * N - n * n, N * N) for n in range(N + 1)]
    if name.startswith('ckink'):  # concave kink at m = N*frac
        m = max(1, (N * int(name[5:])) // 4); return [F(min(n, m), N) for n in range(N + 1)]
    if name.startswith('vkink'):  # convex kink
        m = (N * int(name[5:])) // 4; return [F(max(n - m, 0), N) for n in range(N + 1)]

def kappa_max(d, g, r):
    # largest kappa with rho_N <= 1 and b nondecreasing; b_n = (1 - r - kappa g_n) d_n
    lo, hi = F(0), (1 - r) / g[-1] if g[-1] > 0 else F(1)
    def ok(k):
        b = [(1 - r - k * gn) * dn for gn, dn in zip(g, d)]
        return all(b[i + 1] >= b[i] for i in range(len(b) - 1))
    if ok(hi): return hi
    for _ in range(30):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo

if __name__ == '__main__':
    Nmax = int(sys.argv[1]); t0 = time.time(); count = 0; neg = 0
    Nmin = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else ['lin', 'quad_convex', 'quad_concave', 'ckink1', 'ckink2', 'ckink3', 'vkink1', 'vkink2', 'vkink3']
    qs = [x if x[0] in 'pc' else F(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else [F(1), F(11, 10), F(3, 2)]
    rs = [F(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else [F(1, 5), F(1, 2), F(4, 5)]
    for N in range(Nmin, Nmax + 1):
        for q in qs:
            d = profile(N, q)
            for name in fams:
                g = gfun(name, N)
                for r in rs:
                    km = kappa_max(d, g, r)
                    for lam in [F(1, 2), F(1)]:
                        k = km * lam
                        c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                        b = [dn - cn for dn, cn in zip(d, c)]
                        a = [1 - dn for dn in d]
                        x = first_negative(linearization(a, b, c)); count += 1
                        if x:
                            neg += 1
                            print(f"NEG N={N} q={q} {name} r={r} lam={lam} kappa={float(k):.4f} at (m,n,k)={x[:3]} val={float(x[3]):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {count} arrays, {neg} negative, {time.time()-t0:.0f}s", flush=True)
