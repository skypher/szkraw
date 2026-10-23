"""Random search: Newton ratio sequences rho_1..rho_{N-1} (sigma_{k+1} = rho_k sigma_k) with log-violation
V = max_k log10(rho_k / rho_{k-1}) in (0, Vmax]; LC iff V <= 0. Float64 (N <= 20), r in a list; every failure with the
smallest V is confirmed in mpmath. Usage: r1... random_violation.py N samples Vmax rs seed"""
import sys, time
import numpy as np, mpmath as mp
from math import comb
N, S, Vmax = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]); rs = [float(z) for z in sys.argv[4].split(',')]
rng = np.random.default_rng(int(sys.argv[5])); mp.mp.dps = 60
C = np.array([[comb(i, k) for k in range(N + 1)] for i in range(N + 1)], dtype=float)
def minent(d, r, lib=np):
    a = 1 - d; c = r * d; b = (1 - r) * d
    cur = np.eye(N + 1); prev = np.zeros((N + 1, N + 1)); mn = 0.0
    for m in range(N):
        sd = np.zeros_like(cur); sd[1:] = cur[:-1]; su = np.zeros_like(cur); su[:-1] = cur[1:]
        nxt = ((b - b[m])[:, None] * cur - c[m] * prev + c[:, None] * sd + a[:, None] * su) / a[m]
        prev, cur = cur, nxt; mn = min(mn, cur.min())
    return mn
def minent_mp(lr, r):
    sig = [mp.mpf(1)]
    for x in lr: sig.append(sig[-1] * mp.mpf(10) ** mp.mpf(repr(x)))
    D = [mp.fsum(comb(i, k) * sig[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
    d = [v / D[N] for v in D]; rr = mp.mpf(repr(r)); a = [1 - x for x in d]; c = [rr * x for x in d]; b = [(1 - rr) * x for x in d]
    size = N + 1; cur = [[mp.mpf(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[mp.mpf(0)] * size for _ in range(size)]; w = mp.mpf(0)
    for m in range(N):
        nxt = [[((b[i] - b[m]) * cur[i][j] - c[m] * prev[i][j] + (c[i] * cur[i - 1][j] if i else 0) + (a[i] * cur[i + 1][j] if i < N else 0)) / a[m] for j in range(size)] for i in range(size)]
        prev, cur = cur, nxt; w = min(w, min(min(row) for row in cur))
    return w
t0 = time.time(); fails = []
for it in range(S):
    lr = np.sort(rng.uniform(-5, 3, N - 1))[::-1].copy()   # LC base: nonincreasing log-ratios
    nb = rng.integers(1, 4)                                 # add 1-3 upward bumps
    for _ in range(nb):
        k = rng.integers(1, N - 1); lr[k:] += rng.uniform(0, Vmax) * (1 if rng.random() < .5 else 0) or 0
        if rng.random() < .5: lr[k] += rng.uniform(0, Vmax)
    V = max(0.0, max(lr[k] - lr[k - 1] for k in range(1, N - 1)))
    if V <= 0: continue
    sig = np.concatenate([[1.0], 10.0 ** np.cumsum(lr)])
    D = C[:, 1:] @ sig; d = D / D[N]
    for r in rs:
        if minent(d, r) < -1e-9: fails.append((V, r, lr.copy())); break
    if it % 2000 == 0: print(f"[{time.strftime('%H:%M:%S')}] {it}/{S} samples, {len(fails)} float failures, {time.time()-t0:.0f}s", flush=True)
fails.sort(key=lambda f: f[0])
print(f'{len(fails)} float failures; confirming the smallest violations in mpmath:')
shown = 0
for V, r, lr in fails:
    w = minent_mp(lr, r)
    if w < -mp.mpf(10) ** -40:
        print(f'  confirmed: violation 10^{V:.3f} = {10**V:.3g}, r = {r}, min entry {mp.nstr(w, 3)}, log-ratios {np.round(lr, 2).tolist()}'); shown += 1
        if shown >= 3: break
