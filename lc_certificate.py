"""Log-concave Newton criterion (RESEARCH.md); exact symbolic certificate, diagnostics. Needs sympy.

Fraction-free certificate for the log-concave Newton criterion (constant ratio r = R/(R+W), sigma_{k+1} = sigma_k rho_k,
rho_k = x_k + ... + x_{N-1}). Multiplying each recurrence step by (R+W)(D_N - D_m) keeps all entries polynomial:
g(m,n;k) = P_mnk / Q_m with Q_m = prod_{m'<m} (R+W)(D_N - D_m'), which has positive coefficients. Test: every P_mnk has
nonnegative coefficients (a sufficient condition; P need not be reduced).
The criterion: b_i/c_i constant, and the profile d_n = b_n + c_n has Newton coefficients sigma_k = Delta^k d(0) that are
nonnegative and log-concave (sigma_{k+1}/sigma_k nonincreasing). With rho_k = x_k + ... + x_{N-1} and x_i >= 0 every such
sequence with sigma_1 = 1 arises, so a passing size proves property (P) for all members at that N. Passing sizes: N <= 6
(about 30 s for N = 5; N = 6 took 91 min and 1.4 GB with W = 1). The same test with rho nondecreasing (log-convex) fails from N = 4 on, at the corner and deep triples.
"""
import sys, time, threading
import sympy as sp
T0 = time.time(); STATE = {'msg': ''}
def _hb():
    while True:
        time.sleep(60); print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {STATE['msg']}; elapsed {time.time()-T0:.0f}s", flush=True)
threading.Thread(target=_hb, daemon=True).start()

def check(N):
    R, W = sp.symbols('R W'); xs = sp.symbols(f'x1:{N}')
    gens = (R, W) + tuple(xs)
    P = lambda e: sp.Poly(e, *gens, domain='ZZ')
    rho = [sum(xs[k-1:]) for k in range(1, N)]
    sig = [sp.Integer(0), sp.Integer(1)]
    for k in range(2, N+1): sig.append(sp.expand(sig[-1]*rho[k-2]))
    D = [P(sum(sp.binomial(n, k)*sig[k] for k in range(1, n+1)) if n else 0) for n in range(N+1)]
    RW = P(R + W); Rp = P(R); Wp = P(W)
    size = N + 1; zero = P(0)
    cur = [[P(int(i == j)) for j in range(size)] for i in range(size)]   # numerators over Q_0 = 1
    prev = [[zero]*size for _ in range(size)]
    prev_scale = P(1)                     # factor bringing prev's denominator Q_{m-1} up to Q_m
    total = 0; bad = []; mins = []
    def inspect(m, tab):
        nonlocal total
        for n in range(size):
            for k in range(size):
                pol = tab[n][k]
                if pol.is_zero: continue
                if m > n: continue
                total += 1
                cs = pol.coeffs()
                if any(c < 0 for c in cs): bad.append(((m, n, k), sum(1 for c in cs if c < 0), len(cs)))
    inspect(0, cur)
    for m in range(N):
        STATE['msg'] = f'N={N} step m={m}'
        fac = RW*(D[N] - D[m])
        nxt = [[zero]*size for _ in range(size)]
        for i in range(size):
            for j in range(size):
                v = Wp*(D[i] - D[m])*cur[i][j] - Rp*D[m]*prev_scale*prev[i][j]
                if i: v += Rp*D[i]*cur[i-1][j]
                if i < N: v += RW*(D[N] - D[i])*cur[i+1][j]
                nxt[i][j] = v
        prev, cur = cur, nxt
        prev_scale = fac                  # prev (old cur) has denominator Q_m; new cur has Q_{m+1} = Q_m * fac
        inspect(m + 1, cur)
    return total, bad

if __name__ == '__main__':
  for N in [int(x) for x in (sys.argv[1] if len(sys.argv) > 1 else '2,3,4').split(',')]:
    t0 = time.time(); total, bad = check(N)
    print(f'N={N}: {total} nonzero coefficients (m <= n); numerators with negative coefficients: {len(bad)}'
          + (f'; e.g. {bad[:4]} (triple, negative terms, total terms)' if bad else '') + f' ({time.time()-t0:.0f}s)', flush=True)
