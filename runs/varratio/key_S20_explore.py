"""Explore S_{2,0} = M_{0,2} + M_{1,1} and the (L2) reductions (exact). Usage: key_S20_explore.py amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_S_low import pieces
C = math.comb
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
def lc(rng, L):
    ratios = sorted((Fr(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * ratios[0] if u[0] > 0 else Fr(1))
    for r in ratios[1:]: u.append(u[-1] * r)
    return u
seqs = [lc(rng, amax + 4) for _ in range(T)]
for w in [Fr(1, 10), Fr(1, 1000), Fr(1, 10 ** 6), Fr(1), Fr(10), Fr(1000)]:
    seqs.append([1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]); seqs.append([Fr(0), Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)])
stats = {}
def rec(key, v):
    if key not in stats or v < stats[key][0]: stats[key] = (v,) + cur
for a in range(3, amax + 1):
    for idx, u in enumerate(seqs):
        cur = (a, idx)
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        Y = sum(y(n) for n in range(2, a + 1)); Yp = Y - (a - 1) * u[2]
        Xpp, Xp = B - d0, B - d1; K2 = Yp * Xpp + Y * Xp - 4 * d1 * Hs
        M = pieces(u, a); M02, M11 = M(0, 2), M(1, 1)
        V1 = lambda s: sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
        Zs = lambda s: sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
        G2 = (a - 1) * (Yp * Xpp + Y * Xp) - C(a - 1, 2) * (d0 * Yp + d1 * Y) + d1 * (2 * V1(2) - 4 * Zs(2))
        assert M02 == (a - 1) * B * K2 + Fv * G2
        S20 = M02 + M11
        if M02 < 0: rec('M11/(-M02)', float(M11 / -M02))
        if Fv > 0: rec('S20/(F*B*D*Y)', float(S20 / (Fv * B * d1 * Y)) if Y > 0 else 9e9)
        if G2 < 0: rec('(a-1)BK2/(F(-G2))', float((a - 1) * B * K2 / (Fv * -G2)))
        rec('G2 sign', 1 if G2 >= 0 else -1)
        rec('M11 sign', 1 if M11 >= 0 else -1)
        # (L2) reductions
        R = a * (A - d1) * (B - d1) - 8 * d1 * Hs; rec('R (i-reduction)', 1 if R >= 0 else -1)
        R2 = (a - 2) * (A - d1) * (B - d0) - 4 * a * d1 * Hs; rec('R2 (ii-reduction), a>=6', 1 if (R2 >= 0 or a < 6) else -1)
for k, v in stats.items(): print(k, v)
