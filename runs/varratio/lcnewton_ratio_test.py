"""Conjecture (G): log-concave Newton profile d; ratio rho(x) = sum_k rho_k C(x,k) with (rho_k) nonnegative, log-concave,
no internal zeros, rho_0 = r > 0; b = (1 - rho) d nondecreasing  =>  property (P).
Ratio families: 'geo' rho_k = r e^k (rho(x) = r (1+e)^x), 'rand' random LC (rho_{k+1}/rho_k nonincreasing, <= rho_1/r).
The scale e (resp. rho_1) is lam * (largest value keeping b nondecreasing and rho_N <= 1). Full tables for N <= 16,
rows g(m,N;k) beyond. Optional M check (resummation of Theorem 8.9/8.11) for N <= 10.
Usage: lcnewton_ratio_test.py Ns per rs fam seed [M]"""
import sys, time, threading, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from ratio_random import lc_profile
from rowN_probe import rowN
from resum_test import Mmin
from nonlinear_probe import profile

def arr(d, co):
    N = len(d) - 1
    rho = [sum(ck * math.comb(i, k) for k, ck in enumerate(co) if k <= i) for i in range(N + 1)]
    c = [x * y for x, y in zip(rho, d)]; b = [x - y for x, y in zip(d, c)]
    return [1 - x for x in d], b, c, rho

def ok(d, co):
    a, b, c, rho = arr(d, co)
    return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(len(d) - 1))

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); rs = [F(z) for z in sys.argv[3].split(',')]
    fam = sys.argv[4]; rng = random.Random(int(sys.argv[5])); checkM = len(sys.argv) > 6 and sys.argv[6] == 'M'
    total = len(Ns) * per * len(rs); t0 = time.time(); cnt = 0; neg = 0; negM = 0; CUR = {'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} not (P), {negM} M<0, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in Ns:
        tN = time.time()
        for it in range(per):
            d, nu = lc_profile(N, rng) if it % 3 else (profile(N, F(1)), ['linear'])
            vs = sorted((F(rng.randint(0, 20), 20) for _ in range(N)), reverse=True)
            for r in rs:
                CUR['item'] = f"N={N} r={r}"
                if fam == 'geo': cof = lambda e: [r * e ** k for k in range(N + 1)]
                else:
                    def cof(s):
                        co = [r, s]
                        for k in range(2, N + 1): co.append(co[-1] * (s / r) * vs[k - 2])
                        return co
                lo, hi = F(0), F(1)
                while ok(d, cof(hi)): hi *= 2
                for _ in range(40):
                    mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(d, cof(mid)) else (lo, mid)
                lam = rng.choice([F(1), F(1), F(1, 2)]); co = cof(lo * lam)
                a, b, c, rho = arr(d, co)
                if N <= 16: x = first_negative(linearization(a, b, c))
                else:
                    m_, k_, v_ = rowN(a, b, c); x = (m_, N, k_, v_) if v_ < 0 else None
                cnt += 1
                if x:
                    neg += 1
                    print(f"NOTP N={N} r={r} fam={fam} lam={lam} co={[float(z) for z in co[:5]]} rhoN={float(rho[-1]):.4f} nu={nu if isinstance(nu[0], str) else [str(v) for v in nu]} at {x[:3]} val={float(x[3]):.3e}", flush=True)
                if checkM and N <= 10:
                    mn = Mmin(a, b, c)
                    if mn[0] < 0:
                        negM += 1; print(f"MNEG N={N} r={r} min M={float(mn[0]):.3e} at {mn[1]}<-{mn[2]}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {neg} not (P), {negM} M<0", flush=True)
