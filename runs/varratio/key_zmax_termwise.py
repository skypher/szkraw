"""Termwise proof attempt for the z = 1/w endpoint (k >= 1). Lower bound of G:
G >= sum_m u_m P_m with P_m = coef_m/c1 + coef_{m-1}/c1 [m-1>=2] + (ak/(k+1)) y'_m + N'_m - 4(m-1)C(a,m+1) - 4(m-2)C(a,m)[m>=3],
where coef_m (z=0 coefficients) / c1, y'_m = coefficient of u_m in Y' = C(a-1,m)[2<=m<=a-1] + C(a-1,m-1)[3<=m<=a],
N'_m = sum_{i+n-1=m} C(a,i)C(a-1,n) + sum_{i+n=m} C(a,i)C(a-1,n) over 2<=i<=a, 2<=n<=a-1. Checks P_m >= 0. Usage: amax"""
import sys
from math import comb as C
from fractions import Fraction as F
amax = int(sys.argv[1]); bad = []; cnt = 0
for a in range(3, amax + 1):
    for k in range(1, a):
        c1 = C(a - 1, k); ck = F(C(a - 1, k) * (k * a - k - 1), k + 1)
        def coef(n):
            if n < 2 or n > a: return F(0)
            Nn = C(2 * a - 1, n + 1) - C(a, n + 1) - (a - 1) * C(a, n) - a * C(a - 1, n) - C(a - 1, n + 1)
            v = C(a - 1, k) * Nn + ck * C(a, n)
            if 2 <= n <= a - 1: v += 2 * (n - 1) * (a - n) * C(n, k) * C(a, n)
            if n >= 3: v -= 4 * (n - 2) * C(a, n) * sum(C(i, k) for i in range(n, a))
            return F(v)
        for m in range(2, 2 * a + 1):
            ypm = (C(a - 1, m) if 2 <= m <= a - 1 else 0) + (C(a - 1, m - 1) if 3 <= m <= a else 0)
            Np = sum(C(a, i) * C(a - 1, m + 1 - i) for i in range(2, a + 1) if 2 <= m + 1 - i <= a - 1) + \
                 sum(C(a, i) * C(a - 1, m - i) for i in range(2, a + 1) if 2 <= m - i <= a - 1)
            P = coef(m) / c1 + (coef(m - 1) / c1 if m - 1 >= 2 else 0) + F(a * k, k + 1) * ypm + Np
            P -= 4 * (m - 1) * C(a, m + 1) if m + 1 <= a else 0
            P -= 4 * (m - 2) * C(a, m) if 3 <= m <= a else 0
            cnt += 1
            if P < 0: bad.append((a, k, m, float(P)))
print(f'{cnt} coefficients, {len(bad)} negative; first {bad[:8]}')
