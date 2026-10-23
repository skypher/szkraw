"""Stress test of conjecture (G) with steep exponential ratios rho(x) = r B^x (Newton coefficients r (B-1)^k, geometric,
hence log-concave), r = lam * (largest value keeping b nondecreasing and rho_N <= 1). Profiles: linear, geometric
increments q, and random LC Newton profiles. Full tables for N <= 16, rows g(m,N;k) beyond.
Usage: steep_exp_test.py Ns Bs qs lams [rand_per_N] [seed]"""
import sys, time, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from nonlinear_probe import profile
from rowN_probe import rowN
from ratio_random import lc_profile

def run(d, B, lam):
    N = len(d) - 1
    g = [F(B) ** i for i in range(N + 1)]
    def ok(r):
        rho = [r * x for x in g]; b = [(1 - p) * dd for p, dd in zip(rho, d)]
        return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(N))
    lo, hi = F(0), F(1) / g[-1]
    if not ok(hi):
        for _ in range(40):
            mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    else: lo = hi
    r = lo * lam
    rho = [r * x for x in g]; c = [p * dd for p, dd in zip(rho, d)]; b = [dd - cc for dd, cc in zip(d, c)]; a = [1 - dd for dd in d]
    if N <= 16:
        x = first_negative(linearization(a, b, c)); return (x[:3], x[3]) if x else None
    m, k, v = rowN(a, b, c); return ((m, N, k), v) if v < 0 else None

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; Bs = [F(z) for z in sys.argv[2].split(',')]
    qs = [F(z) for z in sys.argv[3].split(',')]; lams = [F(z) for z in sys.argv[4].split(',')]
    per = int(sys.argv[5]) if len(sys.argv) > 5 else 0; rng = random.Random(int(sys.argv[6]) if len(sys.argv) > 6 else 1)
    t0 = time.time(); cnt = 0; neg = 0
    for N in Ns:
        profs = [('q=' + str(q), profile(N, q)) for q in qs] + [('rand', lc_profile(N, rng)[0]) for _ in range(per)]
        for name, d in profs:
            for B in Bs:
                for lam in lams:
                    res = run(d, B, lam); cnt += 1
                    if res:
                        neg += 1; print(f'NOTP N={N} {name} B={B} lam={lam} at {res[0]} val={float(res[1]):.3e}', flush=True)
        print(f'[{time.strftime("%H:%M:%S")}] N={N} done, {cnt} arrays, {neg} not (P), {time.time()-t0:.0f}s', flush=True)
