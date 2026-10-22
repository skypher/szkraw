"""Extreme rays for ratios with nonnegative Newton coefficients at l: s_i = C(i,k) (rho(l+n) = rho(l) + C(n,k+1)), k = 0..a-1.
Evaluate the weakened key L (gamma = 2) at alpha = s_{a-1} R_{l+a-1} (monotone b at the top) for z = 0 and z = 1/u_2,
adversarial and random LC u. Also the weak alpha = s_{a-1} z. Usage: key_binom_rays.py amax"""
import sys, random, math
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_extreme import L
from key_endpoints import Rtop  # noqa (module runs on import; guarded below)

if __name__ == '__main__':
    amax = int(sys.argv[1]); rng = random.Random(4); res = {}
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
            for k in range(0, a):
                s = [F(math.comb(i, k)) for i in range(a)]
                for aname, al in [('weak', s[a - 1] * z), ('strong', s[a - 1] * Rtop(uu, a))]:
                    v = L(uu, a, al, s, F(2))
                    key = (zname, aname)
                    if key not in res or v < res[key][0]: res[key] = (v, a, k, kind)
    for kk, v in sorted(res.items()): print(kk, 'min L =', float(v[0]), 'at a, k, kind =', v[1:])
