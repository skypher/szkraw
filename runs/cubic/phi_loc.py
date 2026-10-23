"""Reduced per-basis keys for the cubic key (families: V shape C(l,2)+l(n-1) for sigma, W shape tau + sigma l,
local cubic family E3 with key weight 0). Phi_b(u, l, a) = A0_b Y' + Y A0''_b - D Q_b at alpha_b = s_b u0/u1,
Q = 4 H1 - 2 V1 - W1. Local pieces: Phi2loc (rho(l+k) = C(k,2), V shape n-1, W shape 1), Phi3loc (rho(l+k) = C(k,3),
no V, no W). main: (1) identities Phi_2 = l Phi_1 + Phi2loc and Phi_3 = C(l,2) Phi_1 + l Phi2loc + Phi3loc (exact);
(2) Phi3loc = s F(z) + 2 s (z+1) T + 2 C(a,3) z Y' + 2 C(a-1,3)(z+1) Y - 4 (z+1) T3 (F of Theorem 8.9); (3) signs of
Phi2loc, Phi3loc on z in [0, 1/q]. Usage: phi_loc.py trials seed"""
import sys, math, random
from fractions import Fraction as F
C = math.comb
def base(u, a):
    U = lambda k: u[k] if 0 <= k < len(u) else 0
    y = lambda n: C(a, n) * U(n)
    d = dict(U=U, y=y, D=U(0) + U(1), z=U(0) / U(1),
             X=sum(y(n) for n in range(1, a + 1)), Y=sum(y(n) for n in range(2, a + 1)),
             Xp=sum(C(a - 2, j) * (U(j) + U(j + 1)) for j in range(1, a - 1)),
             Yp=sum(C(a - 1, j) * (U(j) + U(j + 1)) for j in range(2, a)))
    return d
def red_key(u, a, val, vsh, wsh):
    """val(k): rho(l+k) - rho(l) on the window (local), vsh(n): V shape, wsh: W shape (constant)."""
    b = base(u, a); U, y, D, X, Y, Xp, Yp = b['U'], b['y'], b['D'], b['X'], b['Y'], b['Xp'], b['Yp']
    s = val(a) - val(a - 1); al = s * U(0) / U(1)
    A0 = al * X - (val(a) - val(0)) * U(0)
    A0b = (al + s) * Xp - (val(a - 1) - val(1)) * D
    H1 = sum((n - 2) * y(n) * (al + val(a) - val(n)) for n in range(3, a + 1))
    V1 = sum((n - 2) * C(a, n) * n * vsh(n) * U(n - 1) for n in range(3, a + 1))
    W1 = wsh * sum((n - 2) * C(a, n) * C(n, 2) * U(n - 2) for n in range(3, a + 1))
    return A0 * Yp + Y * A0b - D * (4 * H1 - 2 * V1 - W1)
def Phi1(u, a): return red_key(u, a, lambda k: k, lambda n: 1, 0)
def Phi2loc(u, a): return red_key(u, a, lambda k: C(k, 2), lambda n: n - 1, 1)
def Phi3loc(u, a): return red_key(u, a, lambda k: C(k, 3), lambda n: 0, 0)
def Phi2(u, a, l): return red_key(u, a, lambda k: C(l + k, 2) - C(l, 2), lambda n: l + n - 1, 1)
def Phi3(u, a, l): return red_key(u, a, lambda k: C(l + k, 3) - C(l, 3), lambda n: C(l, 2) + l * (n - 1), l)
def rand_u(rng, a, zfrac=None):
    if rng.random() < .5:
        q = F(rng.randint(1, 100), 10) ** rng.choice([-3, -2, -1, 1]); rat = [q] * a
    else:
        rat = sorted((F(rng.randint(1, 1000), rng.choice([1, 10, 100, 1000])) for _ in range(a)), reverse=True)
    u = [F(0), F(1)]
    for x in rat: u.append(u[-1] * x)
    u = u[:a + 1]; q = u[2]
    u[0] = (1 / q) * (F(rng.choice([0, 3, 7, 10, 10, 10]), 10) if zfrac is None else zfrac)
    return u
if __name__ == '__main__':
    T, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
    bad = 0; worst = {}
    for _ in range(T):
        a = rng.randint(3, 18); l = rng.choice([0, 1, 2, 5, 17, 100]); u = rand_u(rng, a)
        p1, p2l, p3l = Phi1(u, a), Phi2loc(u, a), Phi3loc(u, a)
        bad += Phi2(u, a, l) != l * p1 + p2l
        bad += Phi3(u, a, l) != C(l, 2) * p1 + l * p2l + p3l
        b = base(u, a); z = b['z']; Y, Yp, J = b['Y'], b['Yp'], b['Xp'] - (a - 2)
        H = sum((n - 2) * b['y'](n) for n in range(3, a + 1)); Tt = sum((n - 3) * (a - n) * b['y'](n) for n in range(2, a + 1))
        T3 = sum((n - 2) * (C(a, 3) - C(n, 3)) * b['y'](n) for n in range(3, a + 1)); s = C(a - 1, 2)
        Fz = z * Y * Yp + (z + 1) * Y * J - (z + 1) * (4 * z * H + 2 * Tt)
        bad += p3l != s * Fz + 2 * s * (z + 1) * Tt + 2 * C(a, 3) * z * Yp + 2 * C(a - 1, 3) * (z + 1) * Y - 4 * (z + 1) * T3
        sc = b['D'] * Y
        for nm, v in (('Phi1', p1), ('Phi2loc', p2l / max(a - 1, 1)), ('Phi3loc', p3l / C(a - 1, 2))):
            if nm not in worst or v / sc < worst[nm][0]: worst[nm] = (v / sc, a, float(u[2]), float(z * u[2]))
    print('identity mismatches:', bad)
    for k, v in worst.items(): print(f'{k}: min normalized {float(v[0]):.4g} at a={v[1]} q={v[2]:.3g} zq={v[3]:.2f}')
