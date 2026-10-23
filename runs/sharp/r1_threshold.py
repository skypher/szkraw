"""At r = 1 (b = 0, c = d, a = 1 - d), the smallest log-convex Newton-ratio step x that breaks (P), by bisection in
log x, for the family rho_k = A (k < K), x A (k >= K). mpmath (dps digits); failure = min table entry < -tol*scale.
Prints, per N and A, the minimal threshold over K and the K attaining it. Heartbeat per N.
Usage: r1_threshold.py Ns As dps"""
import sys, time
import mpmath as mp
from math import comb
Ns = [int(z) for z in sys.argv[1].split(',')]; As = [mp.mpf(z) for z in sys.argv[2].split(',')]; mp.mp.dps = int(sys.argv[3])
def min_entry(d):
    N = len(d) - 1; size = N + 1; a = [1 - x for x in d]; c = d
    cur = [[mp.mpf(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[mp.mpf(0)] * size for _ in range(size)]
    worst = (mp.mpf(0), None)
    for m in range(N):
        nxt = []
        for i in range(size):
            row = []
            for j in range(size):
                v = -c[m] * prev[i][j]
                if i: v += c[i] * cur[i - 1][j]
                if i < N: v += a[i] * cur[i + 1][j]
                row.append(v / a[m])
            nxt.append(row)
        prev, cur = cur, nxt
        for i in range(size):
            for j in range(size):
                if cur[i][j] < worst[0]: worst = (cur[i][j], (m + 1, i, j))
    return worst
def profile(N, A, K, x):
    s = [mp.mpf(1)]
    for k in range(1, N): s.append(s[-1] * (A if k < K else x * A))
    D = [mp.fsum(comb(i, k) * s[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
    return [v / D[N] for v in D]
def fails(N, A, K, lx):
    w = min_entry(profile(N, A, K, mp.e ** lx))
    return w[0] < -mp.mpf(10) ** (-(mp.mp.dps - 15)), w
t0 = time.time()
for N in Ns:
    for A in As:
        best = None
        for K in range(2, N):
            hi = mp.mpf(60)   # x up to e^60
            ok, w = fails(N, A, K, hi)
            if not ok: continue
            lo = mp.mpf(0)
            for _ in range(18):
                mid = (lo + hi) / 2
                f, w2 = fails(N, A, K, mid)
                if f: hi, w = mid, w2
                else: lo = mid
            if best is None or hi < best[0]: best = (hi, K, w[1])
        msg = 'none up to x = e^60' if best is None else f'min threshold x = {float(mp.e ** best[0]):.4g} at K = {best[1]}, entry {best[2]}'
        print(f"[{time.strftime('%H:%M:%S')}] N={N} A={float(A):g}: {msg}  ({time.time()-t0:.0f}s)", flush=True)
