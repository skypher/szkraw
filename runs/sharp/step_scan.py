"""Smallest single log-convex violation that breaks (P) near r = 1 (exact first order, near1.py).
Families on N, base geometric sigma_k = q^(k-1):
  jump(K, x): sigma_k multiplied by x for k > K   (ratio jumps up at K; log-convex at K only), x > 1;
  dip(K, x):  sigma_K divided by x                (log-convex at K), x > 1.
Violation measure: v = sigma_{K-1} sigma_{K+1} / sigma_K^2 (= x for jump, x^2 for dip); LC iff v <= 1.
For each N, q, family, K: the smallest grid x that fails. Heartbeat per N. Usage: step_scan.py Nmax"""
import sys, time
from fractions import Fraction as F
from near1 import profile, fails_near1
Nmax = int(sys.argv[1]); t0 = time.time()
XS = [F(101, 100), F(11, 10), F(3, 2), F(2), F(4), F(10), F(100), F(10 ** 4), F(10 ** 6)]
for N in range(4, Nmax + 1):
    for q in (F(1, 10), F(1), F(10)):
        line = []
        for fam in ('jump', 'dip'):
            for K in range(2, N):
                hit = None
                for x in XS:
                    sig = [q ** (k - 1) for k in range(1, N + 1)]
                    if fam == 'jump': sig = [s * (x if k > K else 1) for k, s in enumerate(sig, 1)]
                    else: sig = [s / (x if k == K else 1) for k, s in enumerate(sig, 1)]
                    w = fails_near1(profile(sig, N))
                    if w: hit = (x, w[0], w[1:4]); break
                line.append(f"{fam}{K}:{'-' if hit is None else str(hit[0]) + hit[1][1:3] + str(hit[2])}")
        print(f"[{time.strftime('%H:%M:%S')}] N={N} q={q}: " + ' '.join(line), flush=True)
