"""S_{2,0} and (L2): candidate quadratic forms, Abel tail criterion (exact, coefficient level).
 Sb  = (a-1)[(a-2)E1^(1) + a E2^(1)] - C(a-1,2) A (Y + Y')
 Ka  = (a-1)(Y'X''+YX') - 4a D H*
 W2  = (a-1)(Y'X''+YX') + 2D(V1^(1)+V1^(2)) - 4D(Z1+Z2)
 R   = a(A-d1)(B-d1) - 8 d1 H*                      [(L2)(i)]
 R2  = (a-2)(A-d1)(B-d0) - 4a d1 H*                 [(L2)(ii)]
Usage: key_S20_quad.py amin amax"""
import sys, math
amin, amax = int(sys.argv[1]), int(sys.argv[2])
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
    bad = []; byW = {}
    for (i, j), q in Q.items(): byW.setdefault(i + j, {})[i] = q
    for W, row in sorted(byW.items()):
        t = 0
        for i in range(W // 2, -1, -1):
            t += row.get(i, 0)
            if t < 0: bad.append((W, i)); break
    return bad
res = {}
for a in range(amin, amax + 1):
    e = lambda m: {m: 1}
    A = {m: C(a, m) for m in range(a + 1)}; B = {m: C(a - 1, m) for m in range(a)}
    F = {m: C(a - 1, m - 1) for m in range(1, a + 1)}
    d0 = e(0); d1 = {0: 1, 1: 1}; D = d1
    Bd0 = add((1, B), (-1, d0)); Bd1 = add((1, B), (-1, d1)); Ad1 = add((1, A), (-1, d1))
    Y = {n: C(a, n) for n in range(2, a + 1)}; Yp = add((1, Y), (-(a - 1), e(2)))
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    V1 = lambda s: {n - 1: (n - 2) * C(a, n) * n * C(n - 1, s - 1) for n in range(3, a + 1)}
    Z = lambda s: {n: (n - 2) * C(a, n) * (C(a, s) - C(n, s)) for n in range(3, a + 1)}
    E1 = {}; mul(E1, A, Bd0); mul(E1, d0, F, -(a - 1))
    E2 = {}; mul(E2, A, Bd1); mul(E2, d1, F, -(a - 2))
    YX = {}; mul(YX, Yp, Bd0); mul(YX, Y, Bd1)
    forms = {}
    Sb = {}; mul(Sb, {0: 1}, add((a - 2, {}), ), 0)
    for k, v in E1.items(): Sb[k] = Sb.get(k, 0) + (a - 1) * (a - 2) * v
    for k, v in E2.items(): Sb[k] = Sb.get(k, 0) + (a - 1) * a * v
    mul(Sb, A, add((1, Y), (1, Yp)), -C(a - 1, 2)); forms['Sb'] = Sb
    Ka = {k: (a - 1) * v for k, v in YX.items()}; mul(Ka, D, H, -4 * a); forms['Ka'] = Ka
    W2 = {k: (a - 1) * v for k, v in YX.items()}; mul(W2, D, add((1, V1(1)), (1, V1(2))), 2); mul(W2, D, add((1, Z(1)), (1, Z(2))), -4); forms['W2'] = W2
    R = {}; mul(R, Ad1, Bd1, a); mul(R, d1, H, -8); forms['R'] = R
    R2 = {}; mul(R2, Ad1, Bd0, a - 2); mul(R2, d1, H, -4 * a); forms['R2'] = R2
    for name, Q in forms.items():
        b = tails(Q)
        if b: res.setdefault(name, []).append((a, b[:3]))
for name in ['Sb', 'Ka', 'W2', 'R', 'R2']:
    print(name, 'tail failures:', res.get(name, 'none')[:6] if name in res else 'none')
