"""(2') for (L1'): c' u0 K'' + u1 [c'(Y'X'' + Y X') + D(2 V1 - 4 Z_s)] >= c'' u1 (d0 Y' + d1 Y), s >= 3,
c' = C(a-1,s-1), c'' = C(a-1,s). Exact check; reports failures and the min ratio LHS/RHS. Usage: key_L1_2prime.py amin amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
C = math.comb
amin, amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), random.Random(int(sys.argv[4]))
def lc(rng, L):
    ratios = sorted((Fr(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * ratios[0] if u[0] > 0 else Fr(1))
    for r in ratios[1:]: u.append(u[-1] * r)
    return u
seqs = [lc(rng, amax + 4) for _ in range(T)]
for w in [Fr(1, 10), Fr(1, 100), Fr(1, 10 ** 6), Fr(1), Fr(10), Fr(1000)]:
    seqs.append([1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]); seqs.append([Fr(0), Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)])
fails = 0; cnt = 0; worst = None
for a in range(amin, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        B, d0, d1 = d(a - 1), d(0), d(1); u0, u1 = u[0], u[1]
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
        Xpp, Xp = B - d0, B - d1; K2 = Yp * Xpp + Y * Xp - 4 * d1 * Hs
        for s in range(3, a + 1):
            c1, c2 = C(a - 1, s - 1), C(a - 1, s)
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
            Zs = sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
            lhs = c1 * u0 * K2 + u1 * (c1 * (Yp * Xpp + Y * Xp) + d1 * (2 * V1 - 4 * Zs)); rhs = c2 * u1 * (d0 * Yp + d1 * Y)
            cnt += 1
            if lhs < rhs: fails += 1
            if rhs > 0:
                q = lhs / rhs
                if worst is None or q < worst[0]: worst = (float(q), a, s)
print(f"{cnt} cases: (2') fails in {fails}; min LHS/RHS = {worst}")
