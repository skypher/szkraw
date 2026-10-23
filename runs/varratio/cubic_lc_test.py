"""Test the conjecture: log-concave Newton profile d, rho(x) = r + t x + tau C(x,2) + sig C(x,3) with t, tau >= 0,
0 <= r sig <= u t tau, b nondecreasing  =>  M >= 0 (resummation of Theorem 8.11) and property (P), at every r.
Random directions (t, tau) scaled by lam * (largest scale keeping b nondecreasing), sig = u t tau / r.
Usage: cubic_lc_test.py Nmin Nmax per_N rs us seed [checkM]"""
import sys, time, threading, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from ratio_random import lc_profile
from cubic_diag import run as diag
from rowN_probe import rowN

def arr(d, r, t, tau, sig):
    N = len(d) - 1
    rho = [r + t * i + tau * math.comb(i, 2) + sig * math.comb(i, 3) for i in range(N + 1)]
    c = [x * y for x, y in zip(rho, d)]; b = [x - y for x, y in zip(d, c)]
    return [1 - x for x in d], b, c, rho

def ok(d, r, t, tau, sig):
    a, b, c, rho = arr(d, r, t, tau, sig)
    return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(len(d) - 1))

if __name__ == '__main__':
    Nmin, Nmax, per = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rs = [F(x) for x in sys.argv[4].split(',')]; us = [F(x) for x in sys.argv[5].split(',')]
    rng = random.Random(int(sys.argv[6])); checkM = len(sys.argv) > 7 and sys.argv[7] == 'M'
    total = (Nmax - Nmin + 1) * per * len(rs) * len(us); t0 = time.time(); cnt = 0; negP = 0; negM = 0; CUR = {'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {negP} not (P), {negM} M<0, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for _ in range(per):
            d, nu = lc_profile(N, rng)
            t1, tau1 = F(rng.choice([0, 1, 1, 2, 5])), F(rng.choice([0, 1, 1, 3, 10]))
            if t1 == 0 and tau1 == 0: t1 = F(1)
            for r in rs:
                for u in us:
                    CUR['item'] = f"N={N} r={r} u={u}"
                    sg = lambda lam: u * (lam * t1) * (lam * tau1) / r
                    lo, hi = F(0), F(1)
                    while ok(d, r, hi * t1, hi * tau1, sg(hi)): hi *= 2
                    for _ in range(40):
                        mid = (lo + hi) / 2
                        lo, hi = (mid, hi) if ok(d, r, mid * t1, mid * tau1, sg(mid)) else (lo, mid)
                    lam = lo * rng.choice([F(1), F(1), F(1, 2)])
                    t, tau, sig = lam * t1, lam * tau1, sg(lam)
                    a, b, c, rho = arr(d, r, t, tau, sig)
                    if N <= 18: x = first_negative(linearization(a, b, c))
                    else:
                        m_, k_, v_ = rowN(a, b, c); x = (m_, N, k_, v_) if v_ < 0 else None
                    cnt += 1
                    if checkM:
                        out = diag(N, r, t, tau, sig, d=d)
                        if out['M'][0] < 0:
                            negM += 1
                            print(f"MNEG N={N} r={r} u={u} t={float(t):.4g} tau={float(tau):.4g} sig={float(sig):.4g} M={float(out['M'][0]):.3e} at {out['M'][1:]} Bdet={float(out['Bdetour'][0]) if out['Bdetour'] else None:.3e}", flush=True)
                    if x:
                        negP += 1
                        print(f"NOTP N={N} r={r} u={u} nu={[str(v) for v in nu]} t={float(t):.4g} tau={float(tau):.4g} sig={float(sig):.4g} at {x[:3]} val={float(x[3]):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {negP} not (P), {negM} M<0", flush=True)
