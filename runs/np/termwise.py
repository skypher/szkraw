"""Is (**) true termwise? For each k, symmetric offset window I = [i0, sp - i0], anti-diagonal tau and each n <= tau/2,
pair value V = 2 P_n F_n(I) - R_n F_n(I-1) - R_{tau-n} F_n(I+1) (n < tau - n) or P_n F_n(I) - R_n F_n(I-1) (n = tau/2),
P_n = C(k,n)C(k,tau-n), R_n = C(k-1,n)C(k+1,tau-n), F_n(J) = sum_{i in J} C(n-1,i) C(tau-n-1, sp-i).
Usage: termwise.py Kmax"""
import sys
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def F(n, m, sp, lo, hi): return sum(C(n - 1, i) * C(m - 1, sp - i) for i in range(lo, hi + 1))
Kmax = int(sys.argv[1]); neg = 0; cnt = 0; worst = None
for k in range(2, Kmax + 1):
    for tau in range(2, 2 * k + 3):
        for sp in range(0, tau - 1):
            for i0 in range(-1, sp // 2 + 1):
                lo, hi = i0, sp - i0
                for n in range(1, tau // 2 + 1):
                    m = tau - n
                    P = C(k, n) * C(k, m); Rn = C(k - 1, n) * C(k + 1, m); Rm = C(k - 1, m) * C(k + 1, n)
                    if n < m: v = 2 * P * F(n, m, sp, lo, hi) - Rn * F(n, m, sp, lo - 1, hi - 1) - Rm * F(n, m, sp, lo + 1, hi + 1)
                    else: v = P * F(n, m, sp, lo, hi) - Rn * F(n, m, sp, lo - 1, hi - 1)
                    cnt += 1
                    if v < 0:
                        neg += 1
                        if worst is None or v < worst[0]: worst = (v, k, tau, sp, i0, n)
print(f'{cnt} pair values, {neg} negative; worst {worst}')
