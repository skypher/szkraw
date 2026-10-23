"""At r = 1 (b = 0): which one-step log-convex Newton profiles fail (P)? Family: Newton ratios rho_k = A (k < K),
B (k >= K); LC iff B <= A. Float64 scan over log10 A, log10 B, K; every failing grid point with the smallest B/A per N
is confirmed in mpmath (60 digits). Prints per N: number of failing points, min violation B/A (confirmed) and where.
Optional r < 1 (b = (1-r) d, c = r d). Usage: r1_grid.py Ns step [r]"""
import sys, time
import numpy as np, mpmath as mp
from math import comb
Ns = [int(z) for z in sys.argv[1].split(',')]; step = float(sys.argv[2]); RR = sys.argv[3] if len(sys.argv) > 3 else '1'
def min_entry_np(d):
    N = len(d) - 1; r = float(RR); a = 1 - d; c = r * d; b = (1 - r) * d
    cur = np.eye(N + 1); prev = np.zeros((N + 1, N + 1)); mn = 0.0
    for m in range(N):
        sd = np.zeros_like(cur); sd[1:] = cur[:-1]; su = np.zeros_like(cur); su[:-1] = cur[1:]
        nxt = ((b - b[m])[:, None] * cur - c[m] * prev + c[:, None] * sd + a[:, None] * su) / a[m]
        prev, cur = cur, nxt; mn = min(mn, cur.min())
    return mn
def min_entry_mp(d):
    N = len(d) - 1; size = N + 1; r = mp.mpf(RR); a = [1 - x for x in d]; c = [r * x for x in d]; b = [(1 - r) * x for x in d]
    cur = [[mp.mpf(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[mp.mpf(0)] * size for _ in range(size)]
    worst = (mp.mpf(0), None)
    for m in range(N):
        nxt = [[((b[i] - b[m]) * cur[i][j] - c[m] * prev[i][j] + (c[i] * cur[i - 1][j] if i else 0) + (a[i] * cur[i + 1][j] if i < N else 0)) / a[m] for j in range(size)] for i in range(size)]
        prev, cur = cur, nxt
        for i in range(size):
            for j in range(size):
                if cur[i][j] < worst[0]: worst = (cur[i][j], (m + 1, i, j))
    return worst
def profile(N, A, B, K, lib):
    s = [lib(1)]
    for k in range(1, N): s.append(s[-1] * (A if k < K else B))
    D = [sum(comb(i, k) * s[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
    return [v / D[N] for v in D]
t0 = time.time(); mp.mp.dps = 60
grid = np.arange(-6, 6 + 1e-9, step)
for N in Ns:
    fails = []
    for K in range(2, N):
        for la in grid:
            for lb in grid:
                if lb <= la: continue
                d = np.array(profile(N, 10.0 ** la, 10.0 ** lb, K, float))
                if min_entry_np(d) < -1e-9: fails.append((lb - la, la, lb, K))
    fails.sort()
    conf = None
    for v, la, lb, K in fails[:20]:
        w = min_entry_mp(profile(N, mp.mpf(10) ** la, mp.mpf(10) ** lb, K, mp.mpf))
        if w[0] < -mp.mpf(10) ** -40: conf = (v, la, lb, K, w); break
    msg = f'{len(fails)} failing grid points' + (f'; min B/A = 10^{conf[0]:.2f} at log A = {conf[1]:.1f}, log B = {conf[2]:.1f}, K = {conf[3]}, entry {conf[4][1]} = {mp.nstr(conf[4][0], 3)} (confirmed)' if conf else '; none confirmed')
    print(f"[{time.strftime('%H:%M:%S')}] r={RR} N={N}: {msg} ({time.time()-t0:.0f}s)", flush=True)
