"""Sufficient coefficient conditions for the cubic weighted B-detour off the corner (exact except sqrt):
after the trade r*sigma <= t*tau (u = 1): all coefficients except r*tau are >= 0, and
k_rtau >= -2 sqrt(k_rr k_tautau) when k_rtau < 0. Reports violations and the tightest margins.
Usage: cubic_quadB_suff.py per seed lmax nmax"""
import sys, math, random
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from cubic_quadB_polar import coeffs
per, rng, lmax, nmax = int(sys.argv[1]), random.Random(int(sys.argv[2])), int(sys.argv[3]), int(sys.argv[4])
profs = [('geo q=%s' % q, [Fr(0)] + [q ** k for k in range(60)]) for q in [Fr(1), Fr(2), Fr(10), Fr(1000), Fr(10 ** 6)]]
for _ in range(per):
    rs = sorted((Fr(rng.randint(1, 80), 10) for _ in range(60)), reverse=True)
    nu = [Fr(0), Fr(1)]
    for x in rs: nu.append(nu[-1] * x)
    profs.append(('rand', nu))
names = ['r', 't', 'tau', 'sig']
viol = {}; rtau_worst = None; cnt = 0
for name, nu in profs:
    for l in range(0, lmax + 1):
        for n in range(2, nmax + 1):
            if (l, n) == (0, 2): continue
            N = l + n + 2
            d = [sum(math.comb(i, kk) * nu[kk] for kk in range(i + 1)) for i in range(N + 1)]
            k = coeffs(d, l, n); g = lambda a, b: k.get((a, b), 0); cnt += 1
            kk = dict(k); kk[(1, 2)] = g(1, 2) + min(g(0, 3), 0); kk[(0, 3)] = max(g(0, 3), 0)
            for key, v in kk.items():
                if key != (0, 2) and v < 0:
                    viol.setdefault(f'{names[key[0]]}*{names[key[1]]}', []).append((name, l, n))
            if g(0, 2) < 0:
                m = 2 * math.sqrt(float(g(0, 0)) * float(g(2, 2))) / -float(g(0, 2))
                if rtau_worst is None or m < rtau_worst[0]: rtau_worst = (m, name, l, n)
print(f'{cnt} cases: violations {[(k, len(v), v[:3]) for k, v in viol.items()]}; '
      f'worst 2sqrt(k_rr k_tautau)/|k_rtau| = {rtau_worst}')
