"""Test (1) the sufficient condition 2A(2B - t) >= (a-2) t F for the main part of S_{sigma,i}, i >= 2, and (2) the full
closed-form S_{sigma,2} = Main - (a-1) d_{l+2} E1^(sigma-2) >= 0, on random and far-field LC u, a up to amax (exact).
Usage: key_S_high_test.py amax trials seed"""
import sys, math, random
from fractions import Fraction as F_
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
C = math.comb
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
def lc(rng, L):
    ratios = sorted((F_(rng.randint(1, 40), 10) for _ in range(L)), reverse=True)
    u = [F_(rng.randint(0, 30), 10)]
    u.append(u[0] * ratios[0] if u[0] > 0 else F_(1))
    for r in ratios[1:]: u.append(u[-1] * r)
    return u
cases = []
for _ in range(T): cases.append(lc(rng, amax + 3))
for w in [F_(1, 10), F_(1, 1000), F_(1, 10 ** 6), F_(1), F_(10)]:
    cases.append([1 / w, F_(1)] + [w ** (n - 1) for n in range(2, amax + 4)])
    cases.append([F_(0), F_(1)] + [w ** (n - 1) for n in range(2, amax + 4)])
bad1 = 0; bad2 = 0; worst1 = None
for a in range(3, amax + 1):
  for u in cases:
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); t = d0 + d1; Fv = A - B
        lhs, rhs = 2 * A * (2 * B - t), (a - 2) * t * Fv
        if lhs < rhs:
            bad1 += 1
            q = float(lhs / rhs)
            if worst1 is None or q < worst1[0]: worst1 = (q, a, [float(x) for x in u[:3]])
        E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
        E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1)
        for s in range(4, 2 * a + 1):
            for i in range(2, s // 2 + 1):
                if s - i > a: continue
                S = sum((C(a, k) * A - ((a - 1) * d2 if k == 2 else 0)) * E1(s - k) + C(a, k) * A * E2(s - k) for k in range(i, s - i + 1))
                if S < 0: bad2 += 1
  print(f'a={a} done: condition failures so far {bad1}, negative S so far {bad2}', flush=True)
print(f'{len(cases)} sequences x a<= {amax}: sufficient condition fails {bad1} (worst ratio {worst1}); S_(sigma,i>=2) < 0 in {bad2}')
