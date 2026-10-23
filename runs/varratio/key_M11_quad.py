"""Candidate reduction for M_{1,1} (exact checks):
  M11 = B0'E1 + B0 E2 + DF(2 nu_1 - 4 Z_1) - 4DBH*,  B0 = a(A-D), E2 = AX' - (a-2)DF.
  With B <= A and FD <= u1 A:  M11 >= B0'E1 + A*Q11 + 2DF nu_1,  Q11 = a(A-D)J - 4DH* - 4u1 Z_1, J = X' - (a-2)u1.
Checks the chain on random LC u (a <= 14) and the Abel tails of Q11 (a <= amax). Usage: key_M11_quad.py amax"""
import sys, math, random, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from key_S_low import pieces
amax = int(sys.argv[1])
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def mul(Q, f, g, c=1):
    for i, x in f.items():
        for j, y in g.items():
            if x and y:
                k = (min(i, j), max(i, j)); Q[k] = Q.get(k, 0) + c * x * y
def add(*fs):
    h = {}
    for c, f in fs:
        for k, v in f.items(): h[k] = h.get(k, 0) + c * v
    return h
def tails(Q):
    byW = {}
    for (i, j), q in Q.items(): byW.setdefault(i + j, {})[i] = q
    for W, row in sorted(byW.items()):
        t = 0
        for i in range(W // 2, -1, -1):
            t += row.get(i, 0)
            if t < 0: return (W, i)
    return None
rng = random.Random(7); bad = 0
for a in range(3, min(14, amax) + 1):
    for _ in range(30):
        r = sorted((Fr(rng.randint(1, 40), 10) for _ in range(a + 3)), reverse=True)
        u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * r[0] if u[0] else Fr(1))
        for x in r[1:]: u.append(u[-1] * x)
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, D = d(a), d(a - 1), u[0] + u[1]; F = A - B; Xpp, Xp = B - u[0], B - D; J = Xp - (a - 2) * u[1]
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        nu1 = sum((n - 2) * C(a, n) * n * u[n - 1] for n in range(3, a + 1)); Z1 = sum((n - 2) * y(n) * (a - n) for n in range(3, a + 1))
        E1 = A * Xpp - (a - 1) * u[0] * F; E2 = A * Xp - (a - 2) * D * F
        B0 = a * (A - D); B0p = a * A - 2 * (a - 1) * (u[0] + 2 * u[1] + u[2]) + (a - 2) * D
        M = pieces(u, a); M11 = M(1, 1)
        bad += M11 != B0p * E1 + B0 * E2 + D * F * (2 * nu1 - 4 * Z1) - 4 * D * B * Hs
        Q11 = a * (A - D) * J - 4 * D * Hs - 4 * u[1] * Z1
        bad += M11 < B0p * E1 + A * Q11 + 2 * D * F * nu1
print('identity/chain failures (a <= 14):', bad)
fails = []
for a in range(3, amax + 1):
    e = lambda m: {m: 1}
    A = {m: C(a, m) for m in range(a + 1)}; D = {0: 1, 1: 1}
    B = {m: C(a - 1, m) for m in range(a)}
    AD = add((1, A), (-1, D)); J = add((1, B), (-1, D), (-(a - 2), e(1)))
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}; Z1 = {n: (n - 2) * C(a, n) * (a - n) for n in range(3, a + 1)}
    Q = {}; mul(Q, AD, J, a); mul(Q, D, H, -4); mul(Q, e(1), Z1, -4)
    t = tails(Q)
    if t: fails.append((a, t))
print('Q11 Abel tail failures:', fails[:10] if fails else 'none', f'(a <= {amax})')
