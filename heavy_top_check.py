"""Exact diagnostics for Theorem 7.12 / Corollary 7.13 (heavy top step) of paper.tex.
(1) Random increasing, generally non-convex, constant-ratio profiles with d_{N-1} <= 1/2: full linearization tables at several r,
    no negative coefficient expected.  (2) Sharpness at N = 2, r = 1: g(2,2;2) = (1 - 2 d_1)/(1 - d_1).
(3) Random non-constant-ratio arrays satisfying (i)-(iii) of Theorem 7.12 with sigma_n = s^n (rejection sampling, N <= 4)."""
import random
from fractions import Fraction as F
from probe import linearization, first_negative

def heavy(rng, N):
    top = F(rng.randint(1, 50), 100); inc = [F(rng.randint(1, 30)) for _ in range(N-1)]; s = sum(inc); d = [F(0)]
    for x in inc: d.append(d[-1] + x/s*top)
    return d + [F(1)]

def theorem_array(rng, N):
    s = F(rng.randint(30, 100), 100)
    c = [F(0)] + sorted(F(rng.randint(1, 100), 100) for _ in range(N))
    b = [F(0)] + sorted(F(rng.randint(0, 100), 100) for _ in range(N)); b[N] = 1 - c[N]
    a = [F(1)] + [1 - x - y for x, y in zip(b[1:], c[1:])]
    if a[N] != 0 or any(x <= 0 for x in a[:N]) or any(b[n+1] < b[n] or c[n+1] < c[n] for n in range(N)): return None
    al = [x/s for x in c]; ga = [a[n]*s for n in range(N)] + [F(0)]
    if any(al[n+1] + ga[n+1] < al[n] + ga[n] for n in range(N)): return None
    if any(ga[i] < al[j] for i in range(N) for j in range(i+1)): return None
    return a, b, c

if __name__ == '__main__':
    rng = random.Random(12); bad = 0; tot = 0
    for N in (3, 4, 5, 6, 8, 10):
        for _ in range(20):
            d = heavy(rng, N)
            for r in (F(1), F(1, 2), F(1, 7)):
                tot += 1; bad += bool(first_negative(linearization([1 - x for x in d], [(1 - r)*x for x in d], [r*x for x in d])))
    print(f'heavy top: {tot} tables (N = 3..10, r in {{1, 1/2, 1/7}}), {bad} with a negative coefficient')
    for x in (F(1, 3), F(1, 2), F(10, 19), F(3, 5)):
        g = linearization([F(1), 1 - x, F(0)], [F(0)]*3, [F(0), x, F(1)])[2][2][2]
        assert g == (1 - 2*x)/(1 - x)
    print('N = 2, r = 1: g(2,2;2) = (1 - 2 d_1)/(1 - d_1) verified at d_1 = 1/3, 1/2, 10/19, 3/5')
    found = bad = 0
    for N in (2, 3, 4):
        for _ in range(200000 if N < 4 else 400000):
            arr = theorem_array(rng, N)
            if arr is None: continue
            found += 1; bad += bool(first_negative(linearization(*arr)))
            if found % 40 == 0: break
    print(f'Theorem 7.12 with sigma_n = s^n: {found} random arrays (N = 2..4), {bad} with a negative coefficient')
