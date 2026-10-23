"""Does L_k(z) := L(C(a-1,k) z, b^{(k)}) dominate C(a-1,k) L_0(z) (L_0 = Theorem 8.9's linear case, slope 1)?
Exact check over random and adversarial LC u, all a <= amax, k, z in {0, 1/u_2, random}. Also reports min L_k.
Usage: key_binom_dom.py amax trials"""
import sys, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_extreme import L
amax, T = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(5)
dom_fail = 0; neg = 0; cnt = 0; worst = None; wdom = None
def us():
    for a in range(3, amax + 1):
        for w in [F(1, 10), F(1), F(10)]:
            yield a, [F(0)] + [w ** (n - 1) for n in range(1, a + 3)]
            for K in [2, 3]:
                yield a, [F(0)] + [w ** (n - 1) if n <= K else F(0) for n in range(1, a + 3)]
    for _ in range(T):
        a = rng.randint(3, amax)
        ratios = sorted((F(rng.randint(0, 40), 10) for _ in range(a + 2)), reverse=True)
        u = [F(0), F(1)]
        for r in ratios: u.append(u[-1] * r)
        yield a, u
for a, u in us():
    w = u[2]
    zs = [F(0)] + ([1 / w, F(rng.randint(0, 100), 100) / w] if w > 0 else [F(rng.randint(0, 50))])
    for z in zs:
        uu = list(u); uu[0] = z
        one = [F(1)] * a
        L0 = L(uu, a, z, one, F(2))
        for k in range(1, a):
            s = [F(math.comb(i, k)) for i in range(a)]
            Lk = L(uu, a, s[a - 1] * z, s, F(2)); cnt += 1
            if Lk < 0:
                neg += 1
                if worst is None or Lk < worst[0]: worst = (Lk, a, k)
            dd = Lk - s[a - 1] * L0
            if dd < 0:
                dom_fail += 1
                if wdom is None or dd < wdom[0]: wdom = (float(dd), a, k, float(z), [float(x) for x in u[1:5]])
print(f'{cnt} (u, z, k>=1) cases: L_k < 0 in {neg}; L_k < C(a-1,k) L_0 in {dom_fail}; worst dom {wdom}')
