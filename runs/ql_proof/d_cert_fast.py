"""d_cert.py with sympy's sparse ring arithmetic (PolyElement over ZZ), much faster than Poly.
Manifest positivity of lemma (D) in LC coordinates; see d_cert.py for the formulas."""
import sys, time, threading
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
from math import comb
T0 = time.time(); ST = {'m': '', 'done': 0, 'total': 0}
def hb():
    while True:
        time.sleep(60); print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {ST['m']}, D numerators checked {ST['done']}; elapsed {time.time()-T0:.0f}s", flush=True)
threading.Thread(target=hb, daemon=True).start()
def run(N):
    names = ['t'] + [f'x{i}' for i in range(1, N)]
    R, *gens = ring(','.join(names), ZZ); t = gens[0]; xs = gens[1:]
    rho = [sum(xs[k-1:], R.zero) for k in range(1, N)]
    sig = [R.zero, R.one]
    for k in range(2, N+1): sig.append(sig[-1]*rho[k-2])
    D = [sum((comb(n, k)*sig[k] for k in range(1, n+1)), R.zero) for n in range(N+1)]
    # entries of H_m actually needed: D at m uses H_m[n-1][k], H_{m-1}[n][k] (m < n <= k); the recurrence for H_{m+1}[n][k]
    # uses H_m[n-1..n+1][k] and H_{m-1}[n][k]. Propagate from the top down; zero by the triangle rule unless |m-n| <= k <= m+n.
    need = {mm: set() for mm in range(N+2)}
    for mm in range(N, -1, -1):
        for n in range(mm+1, N+1):
            for k in range(n, N+1):
                if mm >= 1: need[mm].add((n-1, k)); need[mm-1].add((n, k))
        for (n, k) in list(need.get(mm+1, ())):
            for nn in (n-1, n, n+1):
                if 0 <= nn <= N: need[mm].add((nn, k))
        for (n, k) in list(need.get(mm+2, ())): need[mm].add((n, k))
    prev = [[R.zero]*(N+1) for _ in range(N+1)]; cur = [[R.one if i == j else R.zero for j in range(N+1)] for i in range(N+1)]
    bad = []; tot = 0
    for m in range(N):
        ST['m'] = f'N={N} m={m}'
        prevscale = (D[N] - D[m-1]) if m >= 1 else R.one
        if m >= 1:
            for n in range(m+1, N+1):
                for k in range(n, N+1):
                    num = D[n]*cur[n-1][k] - D[m]*prevscale*prev[n][k]
                    if not num: continue
                    tot += 1; ST['done'] = tot
                    neg = sum(1 for c in num.values() if c < 0)
                    if neg: bad.append(((m, n, k), neg, len(num)))
        nxt = [[R.zero]*(N+1) for _ in range(N+1)]
        for n in range(N+1):
            for k in range(N+1):
                if (n, k) not in need[m+1] or not (abs(m+1-n) <= k <= m+1+n): continue
                v = t*(D[n] - D[m])*cur[n][k] - D[m]*prevscale*prev[n][k]
                if n < N: v += (D[N] - D[n])*cur[n+1][k]
                if n >= 1: v += D[n]*cur[n-1][k]
                nxt[n][k] = v
        prev, cur = cur, nxt
    return tot, bad
for N in [int(x) for x in sys.argv[1].split(',')]:
    t0 = time.time(); tot, bad = run(N)
    print(f'N={N}: {tot} nonzero D numerators, {len(bad)} with a negative coefficient in (t, x)' + (f': {bad[:6]}' if bad else '') + f' ({time.time()-t0:.0f}s)', flush=True)
