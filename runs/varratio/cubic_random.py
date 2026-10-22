"""Random test of the cubic-ratio conjecture: log-concave Newton profile d, rho(x) = r + t x + tau C(x,2) + sig C(x,3)
with t, tau, sig >= 0, b = (1 - rho) d nondecreasing  =>  property (P). Full exact table for N <= 14, row N beyond.
(t, tau, sig) random direction scaled to lam * (largest scale keeping b nondecreasing and rho_N <= 1).
Usage: cubic_random.py Nmin Nmax per_N rs seed"""
import sys, time, threading, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from nonlinear_probe import kappa_max
from rowN_probe import rowN
from ratio_random import lc_profile

if __name__ == '__main__':
    Nmin, Nmax, per = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rs = [F(x) for x in sys.argv[4].split(',')]; rng = random.Random(int(sys.argv[5]))
    total = (Nmax - Nmin + 1) * per * len(rs); t0 = time.time(); cnt = 0; neg = 0; CUR = {'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} negative, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for _ in range(per):
            d, nu = lc_profile(N, rng)
            w = [F(rng.choice([0, 0, 1, 3, 10])) for _ in range(3)]
            if w[2] == 0: w[2] = F(1)
            g = [w[0] * n + w[1] * comb(n, 2) + w[2] * comb(n, 3) for n in range(N + 1)]
            g = [x / g[N] for x in g]
            for r in rs:
                lam = rng.choice([F(1), F(1), F(1, 2)]); CUR['item'] = f"N={N} r={r}"
                k = kappa_max(d, g, r) * lam
                c = [(r + k * gn) * dn for gn, dn in zip(g, d)]; b = [dn - cn for dn, cn in zip(d, c)]; a = [1 - dn for dn in d]
                if N <= 14:
                    x = first_negative(linearization(a, b, c)); bad = x is not None; loc = x[:3] if x else None; val = x[3] if x else 0
                else:
                    m, kk, val = rowN(a, b, c); bad = val < 0; loc = (m, N, kk)
                cnt += 1
                if bad:
                    neg += 1
                    print(f"NEG N={N} r={r} lam={lam} kappa={float(k):.4g} nu={[str(v) for v in nu]} w={[str(v) for v in w]} at {loc} val={float(val):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {neg} negative", flush=True)
