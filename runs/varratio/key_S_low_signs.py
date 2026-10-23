"""Sign structure of the low central sums: S_{sigma,0} = S_{sigma,2} + [M_{1,s-1} + M_{s-1,1}] + M_{0,s} with
M_{0,s} = T1 + T2 + T3 (T1 = C(a-1,s-1) B [A(Y+Y') - 4 D H*] >= 0, T2 = -delta_s (d0 Y' + d1 Y), T3 = D F [2 V1^(s) - 4 sum (n-2) y_n (C(a,s)-C(n,s))]).
Reports, over random and far-field LC u (exact, a <= amax), the min of each part and of useful combinations, normalized by S_{sigma,0}.
Usage: key_S_low_signs.py amax trials seed"""
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
for w in [Fr(1, 10), Fr(1, 1000), Fr(1, 10 ** 6), Fr(1), Fr(10)]:
    seqs.append([1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]); seqs.append([Fr(0), Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)])
stats = {}
def upd(k, v):
    if k not in stats or v < stats[k]: stats[k] = v
for a in range(3, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
        Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        M = pieces(u, a)
        for s in range(2, a + 1):
            dl = C(a, s) * A - C(a - 1, s) * B
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
            T1 = C(a - 1, s - 1) * B * (A * (Y + Yp) - 4 * d1 * Hs)
            T2 = -dl * (d0 * Yp + d1 * Y)
            T3 = d1 * Fv * (2 * V1 - 4 * sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1)))
            S2 = sum(M(k, s - k) for k in range(2, s - 1))
            M1 = M(1, s - 1) + M(s - 1, 1) if s >= 2 else 0
            if s == 2: M1 = M(1, 1)
            S0 = S2 + M1 + T1 + T2 + T3
            if S0 == 0: continue
            for name, v in [('T1', T1), ('T2', T2), ('T3', T3), ('T1+T2', T1 + T2), ('T1+T2+T3', T1 + T2 + T3), ('M1', M1), ('S2+M1', S2 + M1), ('S0', S0)]:
                upd(name, float(v / abs(S0)))
for k in ['T1', 'T2', 'T3', 'T1+T2', 'T1+T2+T3', 'M1', 'S2+M1', 'S0']: print(f'min {k}/|S0| = {stats.get(k, float("nan")):.4g}')
