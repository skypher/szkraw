"""(L1') via a quadratic form. With D = u0 + u1, (2') = D*Q + C(a-1,s) u1^2 Y', where
Q = c'(Y'X'' + Y X') - 4c' u0 H* + u1 (2 V1 - 4 Z_s) - c'' u1 (Y + Y'),  c' = C(a-1,s-1), c'' = C(a-1,s).
Checks the identity on random LC u and the per-weight tail-sum (Abel) criterion for Q and for
K'' = Y'X'' + Y X' - 4 D H*: for every weight W and i0, sum_{i0<=i<=W/2} q_{i,W-i} >= 0.
Usage: key_L1_quad.py amin amax"""
import sys, math, random
from fractions import Fraction as Fr
C = math.comb
amin, amax = int(sys.argv[1]), int(sys.argv[2])
def lin(a, s):
    e = lambda m: {m: 1}
    B = {m: C(a - 1, m) for m in range(a)}
    Xpp = {m: c for m, c in B.items() if m >= 1}; Xp = dict(Xpp); Xp[1] -= 1
    Y = {n: C(a, n) for n in range(2, a + 1)}; Yp = dict(Y); Yp[2] -= a - 1
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    V1 = {n - 1: (n - 2) * C(a, n) * n * C(n - 1, s - 1) for n in range(3, a + 1)}
    Z = {n: (n - 2) * C(a, n) * (C(a, s) - C(n, s)) for n in range(3, a + 1)}
    return B, Xpp, Xp, Y, Yp, H, V1, Z
def mul(Q, f, g, c=1):
    for i, x in f.items():
        for j, y in g.items():
            if x and y:
                k = (min(i, j), max(i, j)); Q[k] = Q.get(k, 0) + c * x * y
def add(f, g, c=1):
    h = dict(f)
    for k, v in g.items(): h[k] = h.get(k, 0) + c * v
    return h
def tails(Q):
    bad = []; byW = {}
    for (i, j), q in Q.items(): byW.setdefault(i + j, {})[i] = q
    for W, row in byW.items():
        t = 0
        for i in range(W // 2, -1, -1):
            t += row.get(i, 0)
            if t < 0: bad.append((W, i, t))
    return bad
def ev(Q, u): return sum(q * u[i] * u[j] for (i, j), q in Q.items())
rng = random.Random(1); nbadQ = nbadK = 0; cnt = 0
for a in range(amin, amax + 1):
    for s in range(3, a + 1):
        B, Xpp, Xp, Y, Yp, H, V1, Z = lin(a, s); c1, c2 = C(a - 1, s - 1), C(a - 1, s)
        Q = {}; mul(Q, Yp, Xpp, c1); mul(Q, Y, Xp, c1); mul(Q, {0: 1}, H, -4 * c1)
        mul(Q, {1: 1}, add(V1, Z, -2), 2); mul(Q, {1: 1}, add(Y, Yp), -c2)
        bQ = tails(Q); cnt += 1
        if bQ: nbadQ += 1; print(f"a={a} s={s}: Q tail failures {bQ[:4]}")
        if a <= 14:  # identity check against the (2') expression
            for _ in range(3):
                r = sorted((Fr(rng.randint(1, 30), 10) for _ in range(a + 2)), reverse=True)
                u = [Fr(rng.randint(0, 20), 10)]; u.append(u[0] * r[0] if u[0] else Fr(1))
                for x in r[1:]: u.append(u[-1] * x)
                d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
                Bv, d0, d1 = d(a - 1), u[0], u[0] + u[1]
                y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
                Yv = sum(y(n) for n in range(2, a + 1)); Ypv = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
                K2 = Ypv * (Bv - d0) + Yv * (Bv - d1) - 4 * d1 * Hs
                V1v = sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
                Zv = sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
                two = c1 * u[0] * K2 + u[1] * (c1 * (Ypv * (Bv - d0) + Yv * (Bv - d1)) + d1 * (2 * V1v - 4 * Zv)) - c2 * u[1] * (d0 * Ypv + d1 * Yv)
                assert two == d1 * ev(Q, u) + c2 * u[1] ** 2 * Ypv, (a, s)
    K = {}; mul(K, Yp, Xpp); mul(K, Y, Xp); mul(K, {0: 1, 1: 1}, H, -4)
    bK = tails(K)
    if bK: nbadK += 1; print(f"a={a}: K'' tail failures {bK[:4]}")
print(f"{cnt} (a,s) pairs, a in [{amin},{amax}]: Q tail criterion fails for {nbadQ}; K'' fails for {nbadK} values of a")
