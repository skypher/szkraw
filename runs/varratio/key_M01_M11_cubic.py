"""M_{0,1} and M_{1,1} as exact cubic forms in u: sign structure and the greedy majorization certificate
(push negative mass from (i,j,k) to (i+1,j,k-1)), as for S_{2,0}. Usage: key_M01_M11_cubic.py amin amax"""
import sys, math, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def cmul(f, g, h, c, T):
    for i, x in f.items():
        for j, y in g.items():
            for k, z in h.items():
                if x and y and z:
                    key = tuple(sorted((i, j, k))); T[key] = T.get(key, 0) + c * x * y * z
def add(*fs):
    h = {}
    for c, f in fs:
        for k, v in f.items(): h[k] = h.get(k, 0) + c * v
    return {k: v for k, v in h.items() if v}
def forms(a):
    e = lambda m: {m: 1}
    A = {m: C(a, m) for m in range(a + 1)}; B = {m: C(a - 1, m) for m in range(a)}
    F = {m: C(a - 1, m - 1) for m in range(1, a + 1)}
    d0 = e(0); d1 = {0: 1, 1: 1}; d2 = {0: 1, 1: 2, 2: 1}; D = d1
    Bd0 = add((1, B), (-1, d0)); Bd1 = add((1, B), (-1, d1))
    Y = {n: C(a, n) for n in range(2, a + 1)}; Yp = add((1, Y), (-(a - 1), e(2)))
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    V1 = {n - 1: (n - 2) * C(a, n) * n for n in range(3, a + 1)}
    Z1 = {n: (n - 2) * C(a, n) * (a - n) for n in range(3, a + 1)}
    B0p1 = add((a, A), (-2 * (a - 1), d2), (a - 2, d1)); B01 = add((a, A), (-a, d1))
    out = {}
    for name, (b0p, b0) in {'M01': (Yp, Y), 'M11': (B0p1, B01)}.items():
        T = {}
        cmul(b0p, A, Bd0, 1, T); cmul(b0p, d0, F, -(a - 1), T)
        cmul(b0, A, Bd1, 1, T); cmul(b0, d1, F, -(a - 2), T)
        cmul(D, F, V1, 2, T); cmul(D, F, Z1, -4, T); cmul(D, B, H, -4, T)
        out[name] = {k: v for k, v in T.items() if v}
    return out
def greedy(T):
    byW = {}
    for (i, j, k), v in T.items(): byW.setdefault(i + j + k, {})[(i, j, k)] = v
    fails = []; maxmin = 0
    for W, row in byW.items():
        row = dict(row)
        for t in sorted([(i, j, W - i - j) for i in range(W + 1) for j in range(i, W + 1) if W - i - j >= j]):
            v = row.get(t, 0)
            if v >= 0: continue
            i, j, k = t; maxmin = max(maxmin, i)
            if k - i < 2: fails.append(t); continue
            nt = tuple(sorted((i + 1, j, k - 1))); row[t] = 0; row[nt] = row.get(nt, 0) + v
    return fails, maxmin
amin, amax = int(sys.argv[1]), int(sys.argv[2])
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from key_S_low import pieces
import random
from fractions import Fraction as Fr
rng = random.Random(3)
for a in range(amin, amax + 1):
    fs = forms(a)
    if a <= 10:  # identity check against M(0,1), M(1,1)
        for _ in range(3):
            u = [Fr(rng.randint(0, 20), 7) for _ in range(a + 3)]
            M = pieces(u, a)
            for name, T in fs.items():
                val = sum(v * u[i] * u[j] * u[k] for (i, j, k), v in T.items())
                assert val == (M(0, 1) if name == 'M01' else M(1, 1)), (a, name)
    res = []
    for name, T in fs.items():
        f, mm = greedy(T)
        pos0 = sum(1 for t, v in T.items() if t[0] == 0 and v > 0)
        res.append(f"{name}: greedy fails {len(f)} (max push level {mm}), positive u0-coefficients {pos0}")
    print(a, ' | '.join(res), flush=True)
