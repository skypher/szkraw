"""Random sweep of the resummation test (M >= 0) for convex quadratic ratios rho_n = r + kappa*(al*x + (1-al)*x^2),
x = n/N, on random log-concave Newton profiles, kappa = lam * kappa_max (b nondecreasing, rho_N <= 1).
Usage: resum_random.py Ns per seed"""
import sys, random, time, math, threading
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from resum_test import Mmin
from rowN_probe import rowN
from nonlinear_probe import kappa_max
from hform import lc_seq
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    t0 = time.time(); st = {'n': 0, 'neg': 0, 'pneg': 0}
    def hb():
        while True:
            time.sleep(60); print(f"[{time.strftime('%H:%M:%S')}] heartbeat {st}", flush=True)
    threading.Thread(target=hb, daemon=True).start()
    for N in Ns:
        for _ in range(per):
            sig = lc_seq(rng, N)
            D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
            d = [x / D[N] for x in D]
            al = F(rng.randint(0, 10), 10); r = F(rng.randint(1, 19), 20)
            g = [al * F(n, N) + (1 - al) * F(n * n, N * N) for n in range(N + 1)]
            km = kappa_max(d, g, r); lam = F(rng.randint(1, 10), 10) if rng.random() < .6 else F(1)
            k = km * lam
            c = [(r + k * gn) * dn for gn, dn in zip(g, d)]; b = [dn - cn for dn, cn in zip(d, c)]; a = [1 - dn for dn in d]
            mn = Mmin(a, b, c); row = rowN(a, b, c); st['n'] += 1
            if mn[0] < 0:
                st['neg'] += 1; print(f"Mneg N={N} al={al} r={r} lam={lam} minM={float(mn[0]):.3e} sig={[float(x) for x in sig]}", flush=True)
            if row[2] < 0:
                st['pneg'] += 1; print(f"PNEG N={N} al={al} r={r} lam={lam}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done {st} {time.time()-t0:.0f}s", flush=True)
