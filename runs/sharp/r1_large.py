"""Targeted mpmath check at larger N near the minimal one-step violation found by r1_grid.py (K = 2, A ~ 1e-3):
does a smaller violation B/A fail as N grows? Usage: r1_large.py Ns r dps"""
import sys, time
import mpmath as mp
from math import comb
Ns = [int(z) for z in sys.argv[1].split(',')]; RR = sys.argv[2]; mp.mp.dps = int(sys.argv[3])
def min_entry(d):
    N = len(d) - 1; size = N + 1; r = mp.mpf(RR); a = [1 - x for x in d]; c = [r * x for x in d]; b = [(1 - r) * x for x in d]
    cur = [[mp.mpf(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[mp.mpf(0)] * size for _ in range(size)]
    worst = mp.mpf(0)
    for m in range(N):
        nxt = [[((b[i] - b[m]) * cur[i][j] - c[m] * prev[i][j] + (c[i] * cur[i - 1][j] if i else 0) + (a[i] * cur[i + 1][j] if i < N else 0)) / a[m] for j in range(size)] for i in range(size)]
        prev, cur = cur, nxt
        worst = min(worst, min(min(row) for row in cur))
    return worst
def profile(N, A, B, K):
    s = [mp.mpf(1)]
    for k in range(1, N): s.append(s[-1] * (A if k < K else B))
    D = [mp.fsum(comb(i, k) * s[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
    return [v / D[N] for v in D]
t0 = time.time()
for N in Ns:
    best = None
    for K in (2, 3):
        for la in (-5, -4, -3.5, -3, -2.5, -2):
            for v in (0.5, 1, 1.5, 2, 2.5):
                w = min_entry(profile(N, mp.mpf(10) ** la, mp.mpf(10) ** (la + v), K))
                if w < -mp.mpf(10) ** (-(mp.mp.dps - 20)) and (best is None or v < best[0]): best = (v, la, K, w)
    print(f"[{time.strftime('%H:%M:%S')}] r={RR} N={N}: " + ('no failure with B/A <= 10^2.5' if best is None else f'min B/A = 10^{best[0]} (log A = {best[1]}, K = {best[2]}, min entry {mp.nstr(best[3], 3)})') + f' ({time.time()-t0:.0f}s)', flush=True)
