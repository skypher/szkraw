"""Extreme-ray reduction of the weakened key (K') for convex ratios. With u_n = f_n(l) (LC, u_1 = 1, u_0 = z), y_n = C(a,n)u_n,
X = sum_{n>=1} y_n, Y = sum_{n>=2} y_n, X' = sum_{j>=1} C(a-2,j)(u_j+u_{j+1}), Y' = sum_{n>=2} C(a-1,n)(u_n+u_{n+1}), D = z+1:
L(alpha, s) = [alpha X - S(0,a-1) z] Y' + Y [(alpha + s_{a-1}) X' - S(1,a-2) D]
              - D [4 sum_{n>=3}(n-2) y_n (alpha + S(n,a-1)) - g sum_{m=2}^{a-1}(m-1)(a-m) s_m y_m].
Checks K_alpha (coefficient of alpha) >= 0 and L(z, e^{(q)}) >= 0 for all q in [0, a-1] (e^{(q)}_i = [i >= q]).
LC u: random log-concave ratio sequences with u_0 = z in [0, 1/u_2]. Usage: key_extreme.py trials amax seed g"""
import sys, random, math
from fractions import Fraction as F

def L(u, a, alpha, s, g):
    C = math.comb; U = lambda n: u[n] if n < len(u) else F(0)
    y = [C(a, n) * U(n) for n in range(a + 1)]
    X = sum(y[1:]); Y = sum(y[2:]); D = U(0) + U(1)
    Xp = sum(C(a - 2, j) * (U(j) + U(j + 1)) for j in range(1, a - 1))
    Yp = sum(C(a - 1, n) * (U(n) + U(n + 1)) for n in range(2, a))
    S = lambda p, q: sum(s[i] for i in range(p, q + 1))
    lhs = (alpha * X - S(0, a - 1) * U(0)) * Yp + Y * ((alpha + s[a - 1]) * Xp - S(1, a - 2) * D)
    rhs = D * (4 * sum((n - 2) * y[n] * (alpha + S(n, a - 1)) for n in range(3, a + 1))
               - g * sum((m - 1) * (a - m) * s[m] * y[m] for m in range(2, a)))
    return lhs - rhs

if __name__ == '__main__':
    T, amax, rng, g = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3])), F(sys.argv[4])
    badK = 0; bad = {}; cnt = 0; worst = None
    for _ in range(T):
        a = rng.randint(3, amax)
        ratios = sorted((F(rng.randint(0, 40), 10) for _ in range(a + 2)), reverse=True)
        u = [F(0), F(1)]
        for r in ratios: u.append(u[-1] * r)
        q2 = u[2]; z = F(rng.randint(0, 100), 100) * (1 / q2 if q2 > 0 else F(rng.randint(0, 50)))
        u[0] = z
        zero = [F(0)] * a
        if L(u, a, F(1), zero, g) - L(u, a, F(0), zero, g) < 0: badK += 1
        for q in range(0, a):
            s = [F(1) if i >= q else F(0) for i in range(a)]
            v = L(u, a, z, s, g); cnt += 1
            if v < 0:
                bad[q] = bad.get(q, 0) + 1
                if worst is None or v < worst[0]: worst = (v, a, q, [float(x) for x in u[:5]])
    print(f'g={g}: {cnt} extreme cases; K_alpha<0: {badK}; failures by q: {bad}; worst {worst}')
