"""Nonconvexity of property (P) at fixed (N, r) (Section 9); exact, diagnostics.

K(N,r) = G(N,1,r) and the geometric array G(N,q,r) of (eq:parameters), q > 1, are both admitted by Theorem 2.1
(constant ratio b_i/c_i = (1-r)/r, geometric increments). The convex combination (1-lam) K + lam G is again a
stochastic constant-ratio array with b_0 = 0; its increments are proportional to 1 + t q^(i-N), not geometric, where
t = lam (q^N - 1)/((1-lam) N (q-1) q^(N-1)). For each listed (r, N, q, t) it has g(N,N;N) < 0 in exact arithmetic.
So no criterion whose admitted set is convex, such as a system of linear inequalities in the coefficients, admits
both K(N,r) and G(N,q,r) at these sizes.

Option --all adds the exact cases (3/10, 200, 2, 5) and (2/7, 200, 10, 5) (about 1 and 6 minutes) and the case
(1/4, 500, 3, 10) in 150- and 300-digit arithmetic (not an exact sign certificate). Option --scan R: high-precision
search (mpmath, 150 digits) over q in {3/2, 2, 3, 10} and t in {1/10, 3/10, 1/2, 1, 2, 5} for the smallest N on a
list with a negative corner on the segment.
"""
import argparse
import time
from fractions import Fraction as F
from smallr_probe import corner

EXAMPLES = [  # (r, N, q, t)
    (F(4, 5), 10, F(10), F(1)),
    (F(3, 5), 20, F(10), F(2)),
    (F(1, 2), 20, F(10), F(1)),
    (F(2, 5), 60, F(10), F(2)),
    (F(1, 3), 100, F(10), F(2)),
]
LARGE = [(F(3, 10), 200, F(2), F(5)), (F(2, 7), 200, F(10), F(5))]  # exact, about 1 and 6 minutes
HIGH_PRECISION = (F(1, 4), 500, 3, 10)  # 150 and 300 digits

def geometric(N, r, q):
    d = [F(0)]
    for i in range(1, N+1): d.append(d[-1] + q**(i-1))
    d = [x/d[-1] for x in d]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def combination(r, N, q, t):
    u = t*(q**N - 1)/(N*(q - 1)*q**(N-1)); lam = u/(1 + u)
    K, G = geometric(N, r, F(1)), geometric(N, r, q)
    return lam, K, G, [[(1-lam)*x + lam*y for x, y in zip(u, v)] for u, v in zip(K, G)]

def check(r, N, q, t):
    lam, K, G, (a, b, c) = combination(r, N, q, t)
    inc = [(a[i-1] - a[i])/(a[0] - a[1]) for i in range(1, N+1)]
    shape = all(inc[i]*(1 + t*q**(1-N)) == 1 + t*q**(i+1-N) for i in range(N))
    basic = (b[0] == 0 and a[N] == 0 and all(x > 0 for x in a[:N]) and all(x > 0 for x in c[1:])
             and all(x >= 0 for x in b) and all(a[n] + b[n] + c[n] == 1 for n in range(N+1))
             and all(b[n]*r == c[n]*(1-r) for n in range(N+1)))
    return lam, basic, shape, corner(*K), corner(*G), corner(a, b, c)

def corner_mp(a, b, c):
    import mpmath as mp
    N = len(a)-1
    prev = [mp.mpf(0)]*(N+1); cur = [mp.mpf(int(i == N)) for i in range(N+1)]
    for m in range(N):
        inv = 1/a[m]; nxt = []
        for i in range(N+1):
            v = (b[i]-b[m])*cur[i] - c[m]*prev[i]
            if i: v += c[i]*cur[i-1]
            if i < N: v += a[i]*cur[i+1]
            nxt.append(v*inv)
        prev, cur = cur, nxt
    return cur[N]

def segment_mp(r, N, q, t):
    import mpmath as mp
    rr = mp.mpf(r.numerator)/r.denominator
    inc = [1 + t*mp.mpf(q)**(i - N) for i in range(1, N+1)]
    d = [mp.mpf(0)]
    for x in inc: d.append(d[-1] + x)
    d = [x/d[-1] for x in d]
    return corner_mp([1-x for x in d], [(1-rr)*x for x in d], [rr*x for x in d])/(1-rr)**N

def scan(r, Ns):
    import mpmath as mp
    mp.mp.dps = 150
    for N in Ns:
        best = None
        for q in (mp.mpf(3)/2, 2, 3, 10):
            for t in (mp.mpf(1)/10, mp.mpf(3)/10, mp.mpf(1)/2, 1, 2, 5):
                g = segment_mp(r, N, q, t)
                if best is None or g < best[0]: best = (g, q, t)
        print(f'r={r} N={N}: min over the segment grid of g(N,N;N)/(1-r)^N = {mp.nstr(best[0], 5)} '
              f'(q={mp.nstr(best[1], 3)}, t={mp.nstr(best[2], 3)})', flush=True)
        if best[0] < 0: break

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--scan', type=F, help='bias r for the high-precision segment search')
    parser.add_argument('--all', action='store_true', help='also the N = 200 exact cases and the N = 500 high-precision case')
    parser.add_argument('--sizes', default='10,20,30,40,60,80,100,150,200,300')
    args = parser.parse_args()
    if args.scan is not None:
        scan(args.scan, [int(x) for x in args.sizes.split(',')]); return
    for r, N, q, t in EXAMPLES + (LARGE if args.all else []):
        t0 = time.time()
        lam, basic, shape, gK, gG, gA = check(r, N, q, t)
        print(f'r={r} N={N} q={q} t={t}: lambda={float(lam):.6g}; basic conditions and constant ratio {basic}; '
              f'increments proportional to 1+t*q^(i-N) {shape}; g(N,N;N) at K {float(gK):+.3e}, at G {float(gG):+.3e}, '
              f'at the combination {float(gA):+.3e} ({time.time()-t0:.0f}s)', flush=True)

    if args.all:
        import mpmath as mp
        r, N, q, t = HIGH_PRECISION
        for dps in (150, 300):
            mp.mp.dps = dps
            print(f'r={r} N={N} q={q} t={t}, {dps} digits: g(N,N;N)/(1-r)^N on the segment = '
                  f'{mp.nstr(segment_mp(r, N, q, t), 10)}', flush=True)

if __name__ == '__main__':
    main()
