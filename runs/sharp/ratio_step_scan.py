"""Smallest log-convex step in the Newton ratios rho_k = sigma_{k+1}/sigma_k that breaks (P) near r = 1
(exact first order). Family: rho_k = A for k < K, rho_k = x A for k >= K (x > 1: one log-convex step at K, geometric
after). K = 1 means sigma = (1, xA, (xA)^2, ...) (geometric, passes). The segment arrays of Section 9 are K = 2.
For each N, A, K: the smallest grid x that fails. Usage: ratio_step_scan.py Nmin Nmax"""
import sys, time
from fractions import Fraction as F
from near1 import profile, fails_near1
Nmin, Nmax = int(sys.argv[1]), int(sys.argv[2])
XS = [F(11, 10), F(3, 2), F(2), F(4), F(10), F(100), F(10 ** 4), F(10 ** 6), F(10 ** 9)]
def sig_of(N, A, K, x):
    s = [F(1)]
    for k in range(1, N): s.append(s[-1] * (A if k < K else x * A))
    return s
for N in range(Nmin, Nmax + 1):
    for A in (F(1, 100), F(1, 10), F(1), F(10)):
        line = []
        for K in range(2, N):
            hit = None
            for x in XS:
                w = fails_near1(profile(sig_of(N, A, K, x), N))
                if w: hit = (x, w[0], w[1:4]); break
            line.append(f"K{K}:{'-' if hit is None else str(hit[0]) + '/' + hit[1][1:3] + str(hit[2]).replace(' ', '')}")
        print(f"[{time.strftime('%H:%M:%S')}] N={N} A={A}: " + ' '.join(line), flush=True)
