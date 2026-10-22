"""z = 1/w endpoint of the binomial-ray key: verify the identity
w^2 L_k(1/w) = w(1+w) L_k(0) + w Y'[c1 a - c2 + c1 Y] - 4 c1 (1+w) H_*  (u_1 = 1, w = u_2),
then test G' = Y' a k/(k+1) + Y Y' - 4 sum_{n>=3}(n-2)C(a,n)u_{n-1} - 4 H_* >= 0 and the weaker G (with + (1+w)L_k(0)/c1).
Usage: key_zmax_reduce.py trials amax"""
import sys, random, math
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_extreme import L
C = math.comb; T, amax = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(11)
idbad = 0; gneg = 0; gpneg = 0; cnt = 0; worst = None
def seqs():
    for a in range(3, amax + 1):
        for w in [F(1, 10), F(1), F(10)]:
            yield a, [F(0), F(1)] + [w ** (n - 1) for n in range(2, a + 3)]
    for _ in range(T):
        a = rng.randint(3, amax)
        ratios = sorted((F(rng.randint(0, 40), 10) for _ in range(a + 2)), reverse=True)
        u = [F(0), F(1)]
        for r in ratios: u.append(u[-1] * r)
        yield a, u
for a, u in seqs():
    w = u[2]
    if w == 0: continue
    U = lambda n: u[n] if n < len(u) else F(0)
    y = [C(a, n) * U(n) for n in range(a + 1)]; Y = sum(y[2:])
    Yp = sum(C(a - 1, n) * (U(n) + U(n + 1)) for n in range(2, a))
    Hs = sum((n - 2) * y[n] for n in range(3, a + 1))
    for k in range(1, a):
        s = [F(C(i, k)) for i in range(a)]
        c1, c2 = C(a - 1, k), C(a, k + 1)
        u0 = list(u); u0[0] = F(0); uw = list(u); uw[0] = 1 / w
        L0 = L(u0, a, F(0), s, F(2)); Lw = L(uw, a, c1 / w, s, F(2))
        if w * w * Lw != w * (1 + w) * L0 + w * Yp * (c1 * a - c2 + c1 * Y) - 4 * c1 * (1 + w) * Hs: idbad += 1
        Gp = Yp * F(a * k, k + 1) + Y * Yp - 4 * sum((n - 2) * C(a, n) * U(n - 1) for n in range(3, a + 1)) - 4 * Hs
        G = Gp + (1 + w) * L0 / c1
        cnt += 1; gneg += G < 0; gpneg += Gp < 0
        if Gp < 0 and (worst is None or Gp < worst[0]): worst = (float(Gp), a, k, [float(x) for x in u[1:5]])
print(f'{cnt} cases: identity mismatches {idbad}; G<0: {gneg}; Gprime<0: {gpneg}; worst Gprime {worst}')
