"""Termwise proof attempt for L_k(0) >= 0 (k >= 1). With u_1 = 1 and LC, YJ >= sum_n N_n u_n,
N_n = C(2a-1,n+1) - C(a,n+1) - (a-1)C(a,n) - a C(a-1,n) - C(a-1,n+1). Coefficient of u_n in the lower bound of L_k(0):
coef_n = C(a-1,k) N_n + c_k C(a,n) + 2(n-1)(a-n)C(n,k)C(a,n)[2<=n<=a-1] - 4(n-2)C(a,n) sum_{i=n}^{a-1} C(i,k) [n>=3],
c_k = C(a-1,k)(ka-k-1)/(k+1). Checks coef_n >= 0 for 2 <= n <= a, 1 <= k <= a-1, 3 <= a <= amax. Usage: key_z0_termwise.py amax"""
import sys
from math import comb as C
from fractions import Fraction as F
amax = int(sys.argv[1]); bad = []; cnt = 0
for a in range(3, amax + 1):
    for k in range(1, a):
        ck = F(C(a - 1, k) * (k * a - k - 1), k + 1)
        for n in range(2, a + 1):
            Nn = C(2 * a - 1, n + 1) - C(a, n + 1) - (a - 1) * C(a, n) - a * C(a - 1, n) - C(a - 1, n + 1)
            coef = C(a - 1, k) * Nn + ck * C(a, n)
            if 2 <= n <= a - 1: coef += 2 * (n - 1) * (a - n) * C(n, k) * C(a, n)
            if n >= 3: coef -= 4 * (n - 2) * C(a, n) * sum(C(i, k) for i in range(n, a))
            cnt += 1
            if coef < 0: bad.append((a, k, n, float(coef)))
print(f'{cnt} coefficients, {len(bad)} negative; first: {bad[:8]}')
