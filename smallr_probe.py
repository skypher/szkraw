"""Convex-profile counterexamples at small r (Section 8); exact, diagnostics.

Constant-ratio arrays a = 1 - d, b = (1-r) d, c = r d with a convex one-kink profile d: m unit increments,
then N - m increments 1 + delta. Each listed array has g(N,N;N) < 0, computed exactly from column N of the
product table (T_{m+1} = (J T_m - b_m T_m - c_m T_{m-1})/a_m restricted to one column, O(N^2) operations).
The onset size grows roughly like 5/r^2, so checks at small N say nothing about small r.

Also listed: counterexamples to the log-concave convex class (increments with nonincreasing step ratios
>= 1): k steps of ratio 1 + 1/(2N), then flat increments.
"""
import argparse
import time
from fractions import Fraction as F

def corner(a, b, c):
    N = len(a)-1
    prev = [F(0)]*(N+1); cur = [F(int(i == N)) for i in range(N+1)]
    for m in range(N):
        nxt = []
        for i in range(N+1):
            v = (b[i]-b[m])*cur[i] - c[m]*prev[i]
            if i: v += c[i]*cur[i-1]
            if i < N: v += a[i]*cur[i+1]
            nxt.append(v/a[m])
        prev, cur = cur, nxt
    return cur[N]

def onekink(N, m, delta, r):
    inc = [F(1)]*m + [1+delta]*(N-m)
    d = [F(0)]
    for x in inc: d.append(d[-1]+x)
    d = [x/d[-1] for x in d]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

COUNTEREXAMPLES = [  # (r, N, m, delta)
    (F(2, 5), 20, 12, F(1, 20)),
    (F(1, 3), 40, 28, F(1, 5)),
    (F(3, 10), 40, 28, F(1, 10)),
    (F(1, 4), 60, 45, F(1, 10)),
    (F(2, 7), 80, 60, F(1, 5)),
    (F(1, 5), 100, 80, F(1, 10)),
    (F(1, 10), 500, 450, F(1, 10)),
]

def logconcave(N, k, r):
    q = 1 + F(1, 2*N)
    inc = [F(1)]
    for _ in range(k): inc.append(inc[-1]*q)
    while len(inc) < N: inc.append(inc[-1])
    ratios = [inc[i+1]/inc[i] for i in range(N-1)]
    assert all(ratios[i] >= ratios[i+1] >= 1 for i in range(N-2))
    d = [F(0)]
    for x in inc: d.append(d[-1]+x)
    d = [x/d[-1] for x in d]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

LOGCONCAVE_COUNTEREXAMPLES = [  # (r, N, k)
    (F(1, 2), 80, 40),
    (F(2, 5), 32, 22),
    (F(1, 3), 90, 62),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--skip-large', action='store_true', help='skip the N = 500 case (about 15 s)')
    parser.add_argument('--highprec', action='store_true',
                        help='also check the log-concave counterexamples at r = 1/4 (N = 250) and r = 1/5 (N = 500) '
                             'at 80 and 150 digits (needs mpmath; about a minute)')
    args = parser.parse_args()
    for r, N, m, delta in COUNTEREXAMPLES:
        if args.skip_large and N > 200: continue
        t0 = time.time()
        g = corner(*onekink(N, m, delta, r))
        print(f'r={r} N={N} m={m} delta={delta}: g(N,N;N) = {float(g):+.4e} '
              f'(negative: {g < 0}; Krawtchouk value (1-r)^N = {float((1-r)**N):.3e}; {time.time()-t0:.0f}s)', flush=True)
    for r, N, k in LOGCONCAVE_COUNTEREXAMPLES:
        g = corner(*logconcave(N, k, r))
        print(f'log-concave convex: r={r} N={N}, {k} steps of ratio 1+1/(2N) then flat: g(N,N;N) = {float(g):+.4e} (negative: {g < 0})', flush=True)
    if args.highprec: highprec()

def highprec():
    import mpmath as mp
    for dps in (80, 150):
        mp.mp.dps = dps
        for r, N, k in ((mp.mpf(1)/4, 250, 175), (mp.mpf(1)/5, 500, 400)):
            q = 1 + mp.mpf(1)/(2*N)
            inc = [mp.mpf(1)]
            for _ in range(k): inc.append(inc[-1]*q)
            while len(inc) < N: inc.append(inc[-1])
            d = [mp.mpf(0)]
            for x in inc: d.append(d[-1]+x)
            d = [x/d[-1] for x in d]
            a = [1-x for x in d]; b = [(1-r)*x for x in d]; c = [r*x for x in d]
            prev = [mp.mpf(0)]*(N+1); cur = [mp.mpf(int(i == N)) for i in range(N+1)]
            for m in range(N):
                nxt = [None]*(N+1)
                for i in range(N+1):
                    v = (b[i]-b[m])*cur[i] - c[m]*prev[i]
                    if i: v += c[i]*cur[i-1]
                    if i < N: v += a[i]*cur[i+1]
                    nxt[i] = v/a[m]
                prev, cur = cur, nxt
            print(f'log-concave convex, {dps} digits: r={mp.nstr(r, 3)} N={N} k={k}: g(N,N;N) = {mp.nstr(cur[N], 6)}', flush=True)

if __name__ == '__main__':
    main()
