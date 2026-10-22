"""Does the key slack S = A0 B0' + B0 A0'' - c (4 H1 - 2 V1) grow when higher Newton coefficients of the ratio are added?
Compare S(rho) with S(rho_lin), rho_lin = rho_0 + rho_1 x (same profile), at every source (l, a), a >= 3, on (G) arrays.
Usage: key_truncation.py Ns per seed"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from g_ingredients import member

def slack(d, co):
    N = len(d) - 1
    rhof = lambda x: sum(ck * math.comb(x, k) for k, ck in enumerate(co) if k <= x)
    rv = [rhof(i) for i in range(2 * N + 3)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    c = [rv[i] * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    f = lambda n, l: dif(d, n, l); phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rv[l + n]) * f(n, l)
    v = lambda n, l: n * dif(rv, 1, l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    out = {}
    for l in range(N):
        for a in range(3, N + 1 - l):
            B0 = W(phi, 2, 0, l, a)
            lhs = (b[l + a] - b[l]) * W(phi, 2, 0, l + 1, a - 1) + B0 * (b[l + a - 1] - b[l + 1])
            out[(l, a)] = lhs - c[l + 1] * (4 * W(h, 3, 1, l, a) - 2 * W(v, 3, 1, l, a))
    return out

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    worse = 0; tot = 0; negS = 0; ex = None
    for N in Ns:
        for it in range(per):
            d, co = member(rng, N, ['mix', 'steep'][it % 2])
            S = slack(d, co); Sl = slack(d, co[:2] + [F(0)] * (len(co) - 2))
            for key in S:
                tot += 1
                if S[key] < 0: negS += 1
                if S[key] < Sl[key]:
                    worse += 1
                    if ex is None: ex = (N, key, float(S[key]), float(Sl[key]), [float(z) for z in co[:4]])
    print(f'{tot} sources: key slack negative {negS}; slack below the linear truncation in {worse}; example {ex}')
