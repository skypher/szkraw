"""S_{2,0} = M_{0,2} + M_{1,1} >= 0: reduction to three quadratic forms (exact checks).
Identity: S20 = B0'E1 + [B0 E2 - c''F(u0 Y' + D Y)] + B Ka + F W2, c'' = C(a-1,2), with
  Ka = (a-1)K'' - 4DH*,  W2 = (a-1)(Y'X''+YX') + D(2V1^(1) + 2V1^(2) - 4Z1 - 4Z2),
  E1 = E1^(1) = A X'' - (a-1)u0 F, E2 = E2^(1) = A X' - (a-2) D F, B0 = a(X'+F), B0' = B0 - 2(a-1)(u1+u2).
Step 1 (FD <= u1 A):  B0 E2 - c''F(u0Y' + DY) >= A Psi,  Psi = a(X'+F)J - c'' u1 (Y + Y'),  J = X' - (a-2)u1.
Step 2 (u1 B >= u0 F, Ka >= 0):  u1(B Ka + F W2) >= F D Qh,  Qh = (a-1)(Y'X''+YX') - 4a u0 H* + u1(2V1^(1)+2V1^(2)-4Z1-4Z2).
Hence u1 S20 >= u1 B0'E1 + u1 A Psi + F D Qh >= 0 once Ka, Psi, Qh >= 0.
Checks: the identity and both steps on random LC u (a <= 14); Abel tail criterion for Ka, Psi, Qh (a <= amax).
Usage: key_S20_proof.py amax"""
import sys, math, random
from fractions import Fraction as Fr
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_S_low import pieces
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
amax = int(sys.argv[1])
C = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def forms(a):
    e = lambda m: {m: 1}
    B = {m: C(a - 1, m) for m in range(a)}; F = {m: C(a - 1, m - 1) for m in range(1, a + 1)}
    D = {0: 1, 1: 1}; Xpp = add((1, B), (-1, e(0))); Xp = add((1, Xpp), (-1, e(1)))
    J = add((1, Xp), (-(a - 2), e(1))); XpF = add((1, Xp), (1, F))
    Y = {n: C(a, n) for n in range(2, a + 1)}; Yp = add((1, Y), (-(a - 1), e(2)))
    H = {n: (n - 2) * C(a, n) for n in range(3, a + 1)}
    V1 = lambda s: {n - 1: (n - 2) * C(a, n) * n * C(n - 1, s - 1) for n in range(3, a + 1)}
    Z = lambda s: {n: (n - 2) * C(a, n) * (C(a, s) - C(n, s)) for n in range(3, a + 1)}
    YX = {}; mul(YX, Yp, Xpp); mul(YX, Y, Xp)
    Ka = {k: (a - 1) * v for k, v in YX.items()}; mul(Ka, D, H, -4 * a)
    Psi = {}; mul(Psi, XpF, J, a); mul(Psi, e(1), add((1, Y), (1, Yp)), -C(a - 1, 2))
    VZ = add((2, V1(1)), (2, V1(2)), (-4, Z(1)), (-4, Z(2)))
    Qh = {k: (a - 1) * v for k, v in YX.items()}; mul(Qh, e(0), H, -4 * a); mul(Qh, e(1), VZ)
    return Ka, Psi, Qh
rng = random.Random(11); bad = 0
for a in range(3, min(amax, 14) + 1):
    for _ in range(40):
        r = sorted((Fr(rng.randint(1, 40), 10) for _ in range(a + 3)), reverse=True)
        u = [Fr(rng.randint(0, 30), 10)]; u.append(u[0] * r[0] if u[0] else Fr(1))
        for x in r[1:]: u.append(u[-1] * x)
        L = lambda f: sum(c * u[m] for m, c in f.items())
        d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
        A, B, D = d(a), d(a - 1), u[0] + u[1]; Fv = A - B; Xpp, Xp = B - u[0], B - D; J = Xp - (a - 2) * u[1]
        y = lambda n: C(a, n) * u[n]; Hs = sum((n - 2) * y(n) for n in range(3, a + 1))
        Y = sum(y(n) for n in range(2, a + 1)); Yp = Y - (a - 1) * u[2]
        V1 = lambda s: sum((n - 2) * C(a, n) * n * C(n - 1, s - 1) * u[n - 1] for n in range(3, a + 1))
        Zs = lambda s: sum((n - 2) * y(n) * (C(a, s) - C(n, s)) for n in range(3, a + 1))
        c2 = C(a - 1, 2); YX = Yp * Xpp + Y * Xp; K2 = YX - 4 * D * Hs
        Ka = (a - 1) * K2 - 4 * D * Hs; W2 = (a - 1) * YX + D * (2 * V1(1) + 2 * V1(2) - 4 * Zs(1) - 4 * Zs(2))
        E1 = A * Xpp - (a - 1) * u[0] * Fv; E2 = A * Xp - (a - 2) * D * Fv; B0 = a * (Xp + Fv); B0p = B0 - 2 * (a - 1) * (u[1] + u[2])
        M = pieces(u, a); S20 = M(0, 2) + M(1, 1)
        bad += S20 != B0p * E1 + (B0 * E2 - c2 * Fv * (u[0] * Yp + D * Y)) + B * Ka + Fv * W2
        Psi = a * (Xp + Fv) * J - c2 * u[1] * (Y + Yp); Qh = (a - 1) * YX - 4 * a * u[0] * Hs + u[1] * (2 * V1(1) + 2 * V1(2) - 4 * Zs(1) - 4 * Zs(2))
        bad += B0 * E2 - c2 * Fv * (u[0] * Yp + D * Y) < A * Psi
        if Ka >= 0: bad += u[1] * (B * Ka + Fv * W2) < Fv * D * Qh
print('identity / step failures on random LC u (a <= 14):', bad)
res = {'Ka': [], 'Psi': [], 'Qh': []}
for a in range(3, amax + 1):
    for name, Q in zip(res, forms(a)):
        if tails(Q): res[name].append(a)
print({k: (v if v else 'none') for k, v in res.items()}, f'(Abel tail failures, a <= {amax})')
