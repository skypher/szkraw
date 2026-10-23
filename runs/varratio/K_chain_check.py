# Checks the chain for K = l_0 (Theorem 8.9 coefficient) on random log-concave u:
#   K >= sum_{n>=3} (n^2-7n+16)/2 * D * C(a,n) u_n >= 0,  D = u0+u1,
# via (i) a u1 Y' >= D sum n C(a,n) u_n, (ii) u2 X' = u2 sum_m C(a-2,m)(u_m+u_{m+1}),
#     (iii) u2 X' >= D sum_{m>=1} C(a-2,m) u_{m+2}.
import random
from math import comb
C = lambda n, k: comb(n, k) if 0 <= k <= n else 0
def dd(u, n): return sum(C(n, h) * u[h] for h in range(n + 1))
def check(u, a):
    A, B = dd(u, a), dd(u, a - 1)
    D0, D1, D2 = u[0], dd(u, 1), dd(u, 2)
    X, Xp = A - D0, B - D1
    Y = A - u[0] - a * u[1]                     # sY
    Yp = A + (a - 2) * D1 - (a - 1) * D2        # beta'_0
    J = Xp - (a - 2) * u[1]                     # sJ
    Hs = sum((n - 2) * C(a, n) * u[n] for n in range(3, a + 1))
    D = u[0] + u[1]
    K = X * Yp + Xp * Y - 4 * D * Hs            # linC f a 0 up to the 1 * D1 = D factor
    ii = a * u[1] * Yp
    rhs_i = D * sum(n * C(a, n) * u[n] for n in range(3, a + 1))
    lhs_ii = u[2] * Xp
    rhs_ii = u[2] * sum(C(a - 2, m) * (u[m] + u[m + 1]) for m in range(1, a - 1))
    rhs_iii = D * sum(C(a - 2, m) * u[m + 2] for m in range(1, a - 1))
    lb = D * sum((n*n - 7*n + 16) / 2 * C(a, n) * u[n] for n in range(3, a + 1))
    eps = 1e-9
    ok = (ii + 0 >= rhs_i - eps * (1 + abs(rhs_i))) and abs(lhs_ii - rhs_ii) < 1e-9 * (1 + abs(lhs_ii)) \
        and lhs_ii >= rhs_iii - eps * (1 + abs(rhs_iii)) and K >= lb - 1e-7 * (1 + abs(lb)) and K >= -1e-9
    return ok, K
random.seed(3)
bad = 0; tot = 0
for t in range(400):
    m = random.randint(4, 12)
    q = sorted([random.uniform(0.05, 3) for _ in range(m)], reverse=True)
    u = [0.0] * 40
    u[1] = random.uniform(0.01, 2); u[0] = random.choice([0.0, random.uniform(0, 1)])
    for k in range(2, m + 2):
        u[k] = u[k - 1] * q[k - 2]
    if u[0] * u[2] > u[1] ** 2: u[0] = u[1] ** 2 / u[2] * 0.99
    for a in range(3, 12):
        ok, K = check(u, a); tot += 1
        if not ok: bad += 1
print("cases", tot, "failures", bad)
