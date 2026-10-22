"""Random test of the conjecture: log-concave Newton profile, ratio rho(x) = r + kappa*sum_j tau_j C(x,j)/C(N,j)
with tau_j >= 0 (nonnegative Newton coefficients of rho), b nondecreasing  =>  property (P), for r <= r0.
Profiles: random log-concave Newton coefficients (nu_1 > 0, ratios nu_{k+1}/nu_k nonincreasing).
kappa = lam * kappa_max (b nondecreasing, rho_N <= 1). Full exact linearization table.
Usage: ratio_random.py Nmin Nmax per_N rs seed"""
import sys, time, threading, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw')
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from nonlinear_probe import kappa_max

def lc_profile(N, rng):
    K = rng.randint(1, N)  # Newton degree
    ratios = sorted((F(rng.randint(0, 40), 20) for _ in range(K - 1)), reverse=True)
    nu = [F(0), F(1)]
    for x in ratios: nu.append(nu[-1] * x)
    D = [sum(nu[k] * comb(n, k) for k in range(len(nu))) for n in range(N + 1)]
    return [x / D[N] for x in D], nu

def random_g(N, rng):
    D = rng.randint(1, N)
    tau = [F(rng.choice([0, 0, 1, 2, 5, 10]), 1) for _ in range(D)]
    if all(t == 0 for t in tau): tau[-1] = F(1)
    g = [sum(tau[j - 1] * F(comb(n, j), comb(N, j)) for j in range(1, D + 1)) for n in range(N + 1)]
    return [x / g[N] for x in g], tau

if __name__ == '__main__':
    Nmin, Nmax, per = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rs = [F(x) for x in sys.argv[4].split(',')]; rng = random.Random(int(sys.argv[5]))
    total = (Nmax - Nmin + 1) * per * len(rs)
    t0 = time.time(); cnt = 0; neg = 0; CUR = {'item': ''}; worst = {}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} negative, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for _ in range(per):
            d, nu = lc_profile(N, rng); g, tau = random_g(N, rng)
            for r in rs:
                lam = rng.choice([F(1), F(1), F(1, 2)])
                CUR['item'] = f"N={N} r={r}"
                k = kappa_max(d, g, r) * lam
                c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                b = [dn - cn for dn, cn in zip(d, c)]
                a = [1 - dn for dn in d]
                x = first_negative(linearization(a, b, c)); cnt += 1
                if x:
                    neg += 1; worst[r] = worst.get(r, 0) + 1
                    print(f"NEG N={N} r={r} lam={lam} kappa={float(k):.4g} nu={[str(v) for v in nu]} tau={[str(t) for t in tau]} at {x[:3]} val={float(x[3]):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {neg} negative", flush=True)
    print(f"failures per r: {dict((str(k), v) for k, v in worst.items())}", flush=True)
