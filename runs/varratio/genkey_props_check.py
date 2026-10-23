# Numerical check of the two Props of lean/Szkraw/GenKey.lean (LinCoefStmt, CentralStmt):
# random log-concave f (no internal zeros), f_1 > 0; a in 3..12.
import random, math
from math import comb

def C(n, k):
    return comb(n, k) if 0 <= k <= n and n >= 0 else 0

def dd(f, n):
    return sum(C(n, h) * f[h] for h in range(n + 1))

def wgt(n):
    return (n - 2) if n >= 3 else 0

def coeffs(f, a):
    A, B = dd(f, a), dd(f, a - 1)
    D0, D1, D2 = f[0], dd(f, 1), dd(f, 2)
    Hs = sum(wgt(n) * C(a, n) * f[n] for n in range(a + 1))
    def zeta(k): return sum(wgt(n) * C(a, n) * f[n] * C(n, k) for n in range(a + 1))
    def nu(k):
        if k < 1: return 0.0
        return sum(wgt(n) * C(a, n) * (n * f[n - 1]) * C(n - 1, k - 1) for n in range(1, a + 1))
    chi = lambda k: C(a, k) * A - C(0, k) * D0
    chip = lambda k: C(a - 1, k) * B - C(1, k) * D1
    beta = lambda k: C(a, k) * A - C(0, k) * D0 - a * (C(1, k) * D1 - C(0, k) * D0)
    betap = lambda k: C(a, k) * A + (a - 2) * C(1, k) * D1 - (a - 1) * C(2, k) * D2
    delta = lambda k: C(a, k) * A - C(a - 1, k) * B
    X, Xp, F = A - D0, B - D1, A - B
    ind = lambda k: 1 if k <= 1 else 0
    lin = lambda k: X * betap(k) + Xp * beta(k) - 4 * ind(k) * D1 * Hs
    M = lambda k, m: (betap(k) * (X * delta(m) - F * chi(m)) + beta(k) * (Xp * delta(m) - F * chip(m))
                      + ind(k) * D1 * (2 * F * nu(m) - 4 * (Hs * delta(m) - F * zeta(m))))
    return lin, M, F

def random_lc(m):
    # f_0..f_m with nonincreasing ratios, positive from index 1 on (f_0 may be 0)
    f1 = random.uniform(0.01, 2.0)
    ratios = sorted([random.uniform(0.01, 3.0) for _ in range(m)], reverse=True)
    f = [0.0, f1]
    for r in ratios[:m - 1]:
        f.append(f[-1] * r)
    f0 = random.choice([0.0, random.uniform(0.0, 1.0)])
    f[0] = f0
    # log-concavity at index 0 needs f0 * f2 <= f1^2
    if f[0] * f[2] > f[1] ** 2:
        f[0] = f[1] ** 2 / f[2] * 0.99
    return f + [0.0] * 20  # zeros after the support (no internal zeros)

worst_lin = 1e300; worst_cen = 1e300
random.seed(1)
for trial in range(300):
    m = random.randint(4, 16)
    f = random_lc(m)
    for a in range(3, 13):
        lin, M, F = coeffs(f, a)
        for k in range(a + 1):
            worst_lin = min(worst_lin, lin(k) / (1 + abs(lin(k))))
        for sigma in range(0, 2 * a + 1):
            for i in range(0, sigma // 2 + 1):
                s = sum(M(k, sigma - k) for k in range(i, sigma - i + 1))
                worst_cen = min(worst_cen, s / (1 + abs(s)))
print("min normalized lin:", worst_lin)
print("min normalized central sum:", worst_cen)
