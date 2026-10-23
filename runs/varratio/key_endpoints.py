"""Endpoint values of the kinked-ratio key L_q (gamma = 2) at z = 0 and z = 1/u_2, with alpha = z (= u0/u1, weak) and with
alpha = R_{l+a-1} = d_{l+a-1}/f_1(l+a-1) (strong, from monotone b at the top). Adversarial u: geometric u_n = w^{n-1} (n>=1),
truncated geometric, and random LC. Usage: key_endpoints.py amax"""
import sys, random, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_extreme import L

def Rtop(u, a):
    U = lambda n: u[n] if n < len(u) else F(0)
    dd = sum(math.comb(a - 1, m) * U(m) for m in range(0, a)); f1 = sum(math.comb(a - 1, m) * U(m + 1) for m in range(0, a))
    return dd / f1
if __name__ == '__main__':
    amax = int(sys.argv[1]); rng = random.Random(3); res = {}
    cases = []
    for a in range(3, amax + 1):
        for w in [F(1, 10), F(1, 2), F(1), F(2), F(10)]:
            cases.append((a, [F(0)] + [w ** (n - 1) for n in range(1, a + 3)], 'geo'))
            for K in [2, 3, 4]:
                cases.append((a, [F(0)] + [w ** (n - 1) if n <= K else F(0) for n in range(1, a + 3)], f'trunc{K}'))
        for _ in range(20):
            ratios = sorted((F(rng.randint(0, 40), 10) for _ in range(a + 2)), reverse=True)
            u = [F(0), F(1)]
            for r in ratios: u.append(u[-1] * r)
            cases.append((a, u, 'rand'))
    for a, u, kind in cases:
        w = u[2]
        for zname, z in [('z0', F(0)), ('zmax', (1 / w) if w > 0 else None)]:
            if z is None: continue
            uu = list(u); uu[0] = z
            for q in range(0, a):
                s = [F(1) if i >= q else F(0) for i in range(a)]
                for aname, al in [('weak', z), ('strong', Rtop(uu, a))]:
                    v = L(uu, a, al, s, F(2))
                    key = (zname, aname)
                    if key not in res or v < res[key][0]: res[key] = (v, a, q, kind)
    for k, v in sorted(res.items()): print(k, 'min L =', float(v[0]), 'at a, q, kind =', v[1:])
