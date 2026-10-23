"""(L1') decomposition: M_{0,s} = C(a-1,s-1) B K'' + F G_s with K'' = Y'X'' + Y X' - 4 D H*, X'' = B - d0, X' = B - d1,
G_s = C(a-1,s-1)(Y'X'' + Y X') - C(a-1,s)(d0 Y' + d1 Y) + D (2 V1^(s) - 4 Z_s). Checks the identity, K'' >= 0, and
min of C(a-1,s-1) B K'' / (F max(-G_s, 0)) (exact). Usage: key_L1_decomp.py amin amax trials seed"""
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
idbad = 0; kneg = 0; ratio = None; gpos = 0; cnt = 0
for a in range(amin, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1 = d(a), d(a - 1), d(0), d(1); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
        Xpp, Xp = B - d0, B - d1
        K2 = Yp * Xpp + Y * Xp - 4 * d1 * Hs
        if K2 < 0: kneg += 1
        for s in range(3, a + 1):
            c1, c2 = C(a - 1, s - 1), C(a - 1, s)
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
            Zs = sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
            E1 = c1 * A * (B - d0) - c2 * d0 * Fv; E2 = c1 * A * (B - d1) - c2 * d1 * Fv
            M0 = Yp * E1 + Y * E2 + 2 * d1 * Fv * V1 - 4 * d1 * (c1 * B * Hs + Fv * Zs)
            G = c1 * (Yp * Xpp + Y * Xp) - c2 * (d0 * Yp + d1 * Y) + d1 * (2 * V1 - 4 * Zs)
            cnt += 1
            if M0 != c1 * B * K2 + Fv * G: idbad += 1
            if G >= 0: gpos += 1
            elif Fv > 0:
                q = c1 * B * K2 / (Fv * (-G))
                if ratio is None or q < ratio[0]: ratio = (float(q), a, s)
print(f'{cnt} cases: identity mismatches {idbad}; K\'\' < 0 in {kneg}; G >= 0 in {gpos}; min C(a-1,s-1) B K\'\'/(F(-G)) = {ratio}')
