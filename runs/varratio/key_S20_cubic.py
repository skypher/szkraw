"""S_{2,0} = M_{0,2} + M_{1,1} as an exact cubic form in u; tree criterion for LC u.
Tree on triples i<=j<=k of weight W, rooted at (0,0,W): parent(i,j,k) = (i-1,j,k+1) if i>=1, else (0,j-1,k+1).
Subtree sums: for i>=1, sum_{t=0}^{j-i} T(i+t,j,k-t); for i=0, the sum over all triples with middle index >= j.
If all are >= 0 the form is >= 0 on LC sequences (Abel summation along the tree). Usage: key_S20_cubic.py amin amax"""
import sys, math, itertools
amin, amax = int(sys.argv[1]), int(sys.argv[2])
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def cmul(f, g, h, c=1, T=None):
    T = {} if T is None else T
    for i, x in f.items():
        for j, y in g.items():
            for k, z in h.items():
                if x and y and z:
                    key = tuple(sorted((i, j, k))); T[key] = T.get(key, 0) + c * x * y * z
    return T
def add(*fs):
    h = {}
    for c, f in fs:
        for k, v in f.items(): h[k] = h.get(k, 0) + c * v
    return {k: v for k, v in h.items() if v}
def qmul(f, g):  # quadratic as list of (f,g) pairs is enough
    return (f, g)
def S20form(a):
    e = lambda m: {m: 1}
    A = {m: C(a, m) for m in range(a + 1)}; B = {m: C(a - 1, m) for m in range(a)}
    F = {m: C(a - 1, m - 1) for m in range(1, a + 1)}
    d0 = e(0); d1 = {0: 1, 1: 1}; d2 = {0: 1, 1: 2, 2: 1}; D = d1
    Bd0 = add((1, B), (-1, d0)); Bd1 = add((1, B), (-1, d1)); Ad0 = add((1, A), (-1, d0)); Ad1 = add((1, A), (-1, d1))
    Y = {n: C(a, n) for n in range(2, a + 1)}; Yp = add((1, Y), (-(a - 1), e(2)))
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    V1 = lambda s: {n - 1: (n - 2) * C(a, n) * n * C(n - 1, s - 1) for n in range(3, a + 1)}
    Z = lambda s: {n: (n - 2) * C(a, n) * (C(a, s) - C(n, s)) for n in range(3, a + 1)}
    T = {}
    # M11 = B0'^(1) E1^(1) + B0^(1) E2^(1) + D E3^(1)
    B0p1 = add((a, A), (-2 * (a - 1), d2), (a - 2, d1)); B01 = add((a, Ad1),)
    # E1^(1) = A(B-d0) - (a-1) d0 F ; E2^(1) = A(B-d1) - (a-2) d1 F
    cmul(B0p1, A, Bd0, 1, T); cmul(B0p1, d0, F, -(a - 1), T)
    cmul(B01, A, Bd1, 1, T); cmul(B01, d1, F, -(a - 2), T)
    # E3^(1) = 2F V1(1) - 4 F Z1 - 4 B H
    cmul(D, F, V1(1), 2, T); cmul(D, F, Z(1), -4, T); cmul(D, B, H, -4, T)
    # M02 = (a-1) B K'' + F G2 ; K'' = Y'X'' + YX' - 4DH ; G2 = (a-1)(Y'X''+YX') - c''(d0Y'+d1Y) + D(2V1(2) - 4Z2)
    c2 = C(a - 1, 2)
    cmul(B, Yp, Bd0, a - 1, T); cmul(B, Y, Bd1, a - 1, T); cmul(B, D, H, -4 * (a - 1), T)
    cmul(F, Yp, Bd0, a - 1, T); cmul(F, Y, Bd1, a - 1, T); cmul(F, d0, Yp, -c2, T); cmul(F, d1, Y, -c2, T)
    cmul(F, D, V1(2), 2, T); cmul(F, D, Z(2), -4, T)
    return {k: v for k, v in T.items() if v}
def check(T, a):
    byW = {}
    for (i, j, k), v in T.items(): byW.setdefault(i + j + k, {})[(i, j, k)] = v
    bad = []; negs = set()
    for W, row in byW.items():
        for (i, j, k), v in row.items():
            if v < 0: negs.add(min(i, 1))
        for j in range(0, W // 2 + 1):  # i = 0 nodes: middle >= j
            if j > W - j: break
            s = sum(v for (i2, j2, k2), v in row.items() if j2 >= j)
            if s < 0: bad.append(('mid>=', W, j, s))
        for (i, j, k) in row:
            if i >= 1:
                s = sum(row.get((i + t, j, k - t), 0) for t in range(0, j - i + 1))
                if s < 0: bad.append(('row', W, (i, j, k), s))
    return bad, negs
if __name__ == '__main__':
    import random
    from fractions import Fraction as Fr
    sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
    from key_S_low import pieces
    rng = random.Random(5)
    for a in range(amin, amax + 1):
        T = S20form(a)
        if a <= 12:
            for _ in range(3):
                u = [Fr(rng.randint(0, 30), 7) for _ in range(a + 3)]
                M = pieces(u, a); val = sum(v * u[i] * u[j] * u[k] for (i, j, k), v in T.items())
                assert val == M(0, 2) + M(1, 1), a
        bad, negs = check(T, a)
        print(f"a={a}: negative coefficients at triples with min index in {sorted(negs)}; tree-criterion failures {len(bad)} {bad[:4]}", flush=True)
