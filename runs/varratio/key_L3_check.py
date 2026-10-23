"""Lemma (L3) check: for k, m >= 2 every term M_{k,m} = B0'^(k) E1^(m) + B0^(k) E2^(m) >= 0, with E1^(m), E2^(m) >= 0
(m >= 1) and C(a,2) A >= (a-1) d_{l+2}. Exact over random and far-field LC u, a <= amax. Usage: key_L3_check.py amax trials seed"""
import sys, math, random
from fractions import Fraction as Fr
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
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
bad = {}
for a in range(3, amax + 1):
    for u in seqs:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2)
        E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
        E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1)
        if C(a, 2) * A < (a - 1) * d2: bad['C(a,2)A<(a-1)d2'] = bad.get('C(a,2)A<(a-1)d2', 0) + 1
        for m in range(2, a + 1):
            if E1(m) < 0: bad['E1'] = bad.get('E1', 0) + 1
            if E2(m) < 0: bad['E2'] = bad.get('E2', 0) + 1
            for k in range(2, a + 1):
                B0p = C(a, k) * A - ((a - 1) * d2 if k == 2 else 0)
                if B0p * E1(m) + C(a, k) * A * E2(m) < 0: bad['M_km'] = bad.get('M_km', 0) + 1
print(f'{len(seqs)} sequences, a <= {amax}: failures {bad if bad else "none"}')
