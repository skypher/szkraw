"""Where is (L1') M_{0,s} >= 0 (s >= 3) tight? Report the 8 smallest ratios pos/neg with (a, s, u-type).
Usage: key_L1_tight.py amin amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
C = math.comb
amin, amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), random.Random(int(sys.argv[4]))
def lc(rng, L):
    ratios = sorted((Fr(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * ratios[0] if u[0] > 0 else Fr(1))
    for r in ratios[1:]: u.append(u[-1] * r)
    return u
seqs = [('rand', lc(rng, amax + 4)) for _ in range(T)]
for w in [Fr(1, 10), Fr(1, 100), Fr(1, 1000), Fr(1, 10 ** 6), Fr(1), Fr(10), Fr(1000)]:
    seqs.append((f'far w={w}', [1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)])); seqs.append((f'near w={w}', [Fr(0), Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]))
rows = []
for a in range(amin, amax + 1):
    for kind, u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1 = d(a), d(a - 1), d(0), d(1); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
        E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
        E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1)
        for s in range(3, a + 1):
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
            Zs = sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
            pos = Yp * E1(s) + Y * E2(s) + 2 * d1 * Fv * V1; neg = 4 * d1 * (C(a - 1, s - 1) * B * Hs + Fv * Zs)
            if neg > 0: rows.append((float(pos / neg), a, s, kind))
rows.sort()
for r in rows[:8]: print(f'ratio {r[0]:.5f} at a={r[1]} s={r[2]} {r[3]}')
