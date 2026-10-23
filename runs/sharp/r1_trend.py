"""Threshold trend at large N (r = 1, K = 2 subfamily, i.e. the mixtures (1-mu) i + mu [i]_q): for each N, the smallest
v in a (sorted) list with B/A = 10^v failing (P) for some log A in a list; the smallest failure found, not a threshold. One line per table with timestamp (progress). Usage: r1_trend.py Ns vs las dps"""
import sys, time
import mpmath as mp
from math import comb
Ns = [int(z) for z in sys.argv[1].split(',')]; vs = sorted(float(z) for z in sys.argv[2].split(',')); las = [float(z) for z in sys.argv[3].split(',')]
mp.mp.dps = int(sys.argv[4])
def min_entry(d):
    N = len(d) - 1; size = N + 1; a = [1 - x for x in d]; c = d
    cur = [[mp.mpf(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[mp.mpf(0)] * size for _ in range(size)]
    worst = (mp.mpf(0), None)
    for m in range(N):
        nxt = [[(-c[m] * prev[i][j] + (c[i] * cur[i - 1][j] if i else 0) + (a[i] * cur[i + 1][j] if i < N else 0)) / a[m] for j in range(size)] for i in range(size)]
        prev, cur = cur, nxt
        for i in range(size):
            for j in range(size):
                if cur[i][j] < worst[0]: worst = (cur[i][j], (m + 1, i, j))
    return worst
def profile(N, A, B):
    s = [mp.mpf(1)]
    for k in range(1, N): s.append(s[-1] * (A if k < 2 else B))
    D = [mp.fsum(comb(i, k) * s[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
    return [v / D[N] for v in D]
t0 = time.time(); tol = mp.mpf(10) ** (-(mp.mp.dps // 2))
for N in Ns:
    for v in vs:
        hit = None
        for la in las:
            w = min_entry(profile(N, mp.mpf(10) ** la, mp.mpf(10) ** (la + v)))
            print(f"[{time.strftime('%H:%M:%S')}] N={N} B/A=10^{v} logA={la}: min {mp.nstr(w[0], 4)} at {w[1]} ({time.time()-t0:.0f}s)", flush=True)
            if w[0] < -tol: hit = (la, w); break
        if hit: print(f"   => N={N}: B/A = 10^{v} FAILS (log A = {hit[0]})", flush=True); break
