"""Lemma (L2): M_{1,m} + M_{m,1} >= 0 (m >= 2). Test candidate splits (exact):
 (i)  B0^(1) E2^(m) >= 4 D C(a-1,m-1) B H*,
 (ii) B0'^(1) E1^(m) + B0'^(m) E1^(1) + B0^(m) E2^(1) + [B0^(1) E2^(m) - 4 D C(a-1,m-1) B H*] >= D F [4 sum (n-2) y_n (C(a,m)-C(n,m)) - 2 V1^(m)],
 and the total. Usage: key_L2_split.py amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
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
bad = {'i': 0, 'ii': 0, 'total': 0}; cnt = 0
for a in range(3, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); Fv = A - B
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
        E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1) + (d1 * Fv if m == 1 else 0)
        B0_1, B0p_1 = a * (A - d1), a * A - 2 * (a - 1) * d2 + (a - 2) * d1
        M = pieces(u, a)
        for m in range(2, a + 1):
            B0p_m = C(a, m) * A - ((a - 1) * d2 if m == 2 else 0); B0_m = C(a, m) * A
            V1 = sum((n - 2) * C(a, n) * n * C(n - 1, m - 1) * u[n - 1] for n in range(3, a + 1))
            lhs_i = B0_1 * E2(m); rhs_i = 4 * d1 * C(a - 1, m - 1) * B * Hs
            rest = B0p_1 * E1(m) + B0p_m * E1(1) + B0_m * E2(1) + (lhs_i - rhs_i)
            rhs_ii = d1 * Fv * (4 * sum((n - 2) * y(n) * (C(a, m) - C(n, m)) for n in range(3, a + 1)) - 2 * V1)
            tot = M(1, m) + M(m, 1); cnt += 1
            bad['i'] += lhs_i < rhs_i; bad['ii'] += rest < rhs_ii; bad['total'] += tot < 0
print(f'{cnt} cases (a <= {amax}): failures {bad}')
