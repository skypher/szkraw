"""End-to-end test of the (C3) theorem at u = 1: log-concave Newton profile d, rho = r + t x + tau C(x,2) + sig C(x,3)
with sig = u t tau / r (u = 1: the boundary r sig = t tau), (t, tau) = lam (t1, tau1), lam bisected to the largest value
keeping b = (1 - rho) d nondecreasing and rho <= 1 (sometimes scaled down). Checks property (P): full exact table for
N <= 14, row N beyond. Heartbeat every 30 s. Usage: c3_property_P.py Nmin Nmax per u seed"""
import sys, os, time, threading, random
from fractions import Fraction as F
from math import comb
_VR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'varratio')
sys.path.insert(0, os.path.join(_VR, '..', '..')); sys.path.insert(0, _VR)
from probe import linearization, first_negative
from rowN_probe import rowN
from ratio_random import lc_profile
if __name__ == '__main__':
    Nmin, Nmax, per, u = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), F(sys.argv[4]); rng = random.Random(int(sys.argv[5]))
    total = (Nmax - Nmin + 1) * per; t0 = time.time(); st = {'cnt': 0, 'neg': 0, 'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {st['cnt']}/{total} arrays, {st['neg']} negative, at {st['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for _ in range(per):
            d, nu = lc_profile(N, rng)
            r = F(rng.choice([1, 10, 50, 90, 99, 999])) / (1000 if rng.random() < .4 else 100); r = min(r, F(999, 1000))
            t1, tau1 = F(rng.choice([1, 1, 10, 1000])), F(rng.choice([1, 10, 1000]))
            mk = lambda lam: (lam * t1, lam * tau1, u * lam * t1 * lam * tau1 / r)
            def ok(lam):
                t, tau, sg = mk(lam); rho = [r + t * i + tau * comb(i, 2) + sg * comb(i, 3) for i in range(N + 1)]
                b = [(1 - rh) * di for rh, di in zip(rho, d)]
                return rho[N] <= 1 and all(b[i + 1] >= b[i] for i in range(N))
            lo, hi = F(0), F(1)
            while ok(hi): hi *= 2
            for _ in range(40):
                mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
            lam = lo * (F(rng.randint(1, 10), 10) if rng.random() < .3 else 1)
            t, tau, sg = mk(lam); st['item'] = f'N={N}'
            rho = [r + t * i + tau * comb(i, 2) + sg * comb(i, 3) for i in range(N + 1)]
            c = [rh * di for rh, di in zip(rho, d)]; b = [di - ci for di, ci in zip(d, c)]; a = [1 - di for di in d]
            if N <= 14:
                x = first_negative(linearization(a, b, c)); bad = x is not None; loc = x[:3] if x else None
            else:
                m_, kk, val = rowN(a, b, c); bad = val < 0; loc = (m_, N, kk)
            st['cnt'] += 1
            if bad:
                st['neg'] += 1
                print(f"NEG N={N} r={r} t={float(t):.3g} tau={float(tau):.3g} sig={float(sg):.3g} nu={[str(v) for v in nu]} at {loc}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {st['cnt']}/{total} arrays, {st['neg']} negative", flush=True)
