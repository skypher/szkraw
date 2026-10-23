"""Test the general-degree conjecture: log-concave Newton profile d; ratio rho(x) = sum_k rho_k C(x,k) with rho_0 = r,
rho_1 = t, rho_2 = tau >= 0 and, for k >= 2, 0 <= r rho_{k+1} <= u t rho_k; b nondecreasing => property (P).
Random t, tau directions and multipliers v_k in [0,1]: rho_{k+1} = u (t/r) v_k rho_k. Scale lam * (largest scale with
b nondecreasing), the higher coefficients recomputed at each scale. Full table for N <= 18, row N beyond.
Usage: ratio_degree_test.py Nmin Nmax per_N rs us seed"""
import sys, time, threading, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from ratio_random import lc_profile
from rowN_probe import rowN

def coeffs(r, t, tau, vs, u):
    co = [r, t, tau]
    for v in vs: co.append(u * (t / r) * v * co[-1])
    return co

def arr(d, co):
    N = len(d) - 1
    rho = [sum(ck * math.comb(i, k) for k, ck in enumerate(co)) for i in range(N + 1)]
    c = [x * y for x, y in zip(rho, d)]; b = [x - y for x, y in zip(d, c)]
    return [1 - x for x in d], b, c, rho

def ok(d, co):
    a, b, c, rho = arr(d, co)
    return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(len(d) - 1))

if __name__ == '__main__':
    Nmin, Nmax, per = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rs = [F(x) for x in sys.argv[4].split(',')]; us = [F(x) for x in sys.argv[5].split(',')]; rng = random.Random(int(sys.argv[6]))
    total = (Nmax - Nmin + 1) * per * len(rs) * len(us); t0 = time.time(); cnt = 0; neg = 0; CUR = {'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} not (P), at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for _ in range(per):
            d, nu = lc_profile(N, rng)
            t1, tau1 = F(rng.choice([1, 1, 2, 5])), F(rng.choice([0, 1, 1, 3, 10]))
            D = rng.randint(3, N)
            vs = [F(rng.choice([0, 1, 2, 3, 4]), 4) for _ in range(D - 2)]
            for r in rs:
                for u in us:
                    CUR['item'] = f"N={N} r={r} u={u}"
                    cof = lambda lam: coeffs(r, lam * t1, lam * tau1, vs, u)
                    lo, hi = F(0), F(1)
                    while ok(d, cof(hi)): hi *= 2
                    for _ in range(40):
                        mid = (lo + hi) / 2
                        lo, hi = (mid, hi) if ok(d, cof(mid)) else (lo, mid)
                    lam = lo * rng.choice([F(1), F(1), F(1, 2)]); co = cof(lam)
                    a, b, c, rho = arr(d, co)
                    if N <= 18: x = first_negative(linearization(a, b, c))
                    else:
                        m_, k_, v_ = rowN(a, b, c); x = (m_, N, k_, v_) if v_ < 0 else None
                    cnt += 1
                    if x:
                        neg += 1
                        print(f"NOTP N={N} r={r} u={u} D={D} co={[float(z) for z in co]} nu={[str(v) for v in nu]} at {x[:3]} val={float(x[3]):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {neg} not (P)", flush=True)
