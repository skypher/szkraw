"""Manifest positivity of lemma (D) in log-concavity coordinates: sigma_1 = 1, sigma_{k+1} = sigma_k rho_k,
rho_k = x_k + ... + x_{N-1} (x >= 0 is exactly LC). Fraction-free H recurrence (v = 1, u = t):
P_{m+1}[n] = t(D_n - D_m) P_m[n] + (D_N - D_n) P_m[n+1] + D_n P_m[n-1] - D_m (D_N - D_{m-1}) P_{m-1}[n],  H_m = P_m / Q_m,
Q_m = prod_{m'<m} (D_N - D_m'), and D_{mn}^k * D_N * Q_m = D_n P_m[n-1] - D_m (D_N - D_{m-1}) P_{m-1}[n].
Reports, for each N, the triples (m < n <= k) whose numerator has a negative coefficient in (t, x)."""
import sys, time, threading
import sympy as sp
T0 = time.time(); ST = {'m': ''}
def hb():
    while True:
        time.sleep(60); print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {ST['m']}; elapsed {time.time()-T0:.0f}s", flush=True)
threading.Thread(target=hb, daemon=True).start()
def run(N):
    t = sp.Symbol('t'); xs = sp.symbols(f'x1:{N}'); gens = (t,) + tuple(xs)
    P = lambda e: sp.Poly(e, *gens, domain='ZZ')
    rho = [sum(xs[k-1:]) for k in range(1, N)]
    sig = [sp.Integer(0), sp.Integer(1)]
    for k in range(2, N+1): sig.append(sp.expand(sig[-1]*rho[k-2]))
    D = [P(sum(sp.binomial(n, k)*sig[k] for k in range(1, n+1)) if n else 0) for n in range(N+1)]
    zero = P(0); tp = P(t)
    prev = [[zero]*(N+1) for _ in range(N+1)]; cur = [[P(int(i == j)) for j in range(N+1)] for i in range(N+1)]
    bad = []; tot = 0
    for m in range(N):
        ST['m'] = f'N={N} m={m}'
        prevscale = (D[N] - D[m-1]) if m >= 1 else P(1)
        # numerators of D_{m,n}^k for m >= 1
        if m >= 1:
            for n in range(m+1, N+1):
                for k in range(n, N+1):
                    num = D[n]*cur[n-1][k] - D[m]*prevscale*prev[n][k]
                    if num.is_zero: continue
                    tot += 1
                    neg = sum(1 for c in num.coeffs() if c < 0)
                    if neg: bad.append(((m, n, k), neg, len(num.coeffs())))
        nxt = [[zero]*(N+1) for _ in range(N+1)]
        for n in range(N+1):
            for k in range(N+1):
                v = tp*(D[n] - D[m])*cur[n][k] - D[m]*prevscale*prev[n][k]
                if n < N: v += (D[N] - D[n])*cur[n+1][k]
                if n >= 1: v += D[n]*cur[n-1][k]
                nxt[n][k] = v
        prev, cur = cur, nxt
    # m = N has no D (needs m < n <= N)
    return tot, bad
for N in [int(x) for x in sys.argv[1].split(',')]:
    t0 = time.time(); tot, bad = run(N)
    print(f'N={N}: {tot} nonzero D numerators, {len(bad)} with a negative coefficient in (t, x)' + (f': {bad[:6]}' if bad else '') + f' ({time.time()-t0:.0f}s)', flush=True)
