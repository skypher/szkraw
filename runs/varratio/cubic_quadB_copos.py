"""After the trade r sigma <= t tau, is the sigma-free part of the cubic weighted B-detour still copositive?
For each profile and (l, n) != (0, 2): Q'(r,t,tau) = Q(r,t,tau) + min(k_rs, 0) t tau, and check
(a) the remaining sigma coefficients k_t,sig, k_tau,sig, k_sig,sig >= 0, (b) Q' copositive on r,t,tau >= 0
(3x3 Hadeler criterion, float; exact for the 2x2 sub-tests). Usage: cubic_quadB_copos.py per seed lmax nmax [u]"""
import sys, math, random
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from cubic_quadB_polar import coeffs
per, rng, lmax, nmax = int(sys.argv[1]), random.Random(int(sys.argv[2])), int(sys.argv[3]), int(sys.argv[4])
U = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(1)
def copos3(A):
    a = [[float(x) for x in row] for row in A]
    if min(a[i][i] for i in range(3)) < 0: return False, 'diag'
    s = [math.sqrt(a[i][i]) for i in range(3)]
    ab = {}
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        ab[(i, j)] = a[i][j] + s[i] * s[j]
        if ab[(i, j)] < -1e-9 * (1 + abs(a[i][j])): return False, ('pair', i, j)
    val = s[0] * s[1] * s[2] + a[0][1] * s[2] + a[0][2] * s[1] + a[1][2] * s[0] + math.sqrt(max(0.0, 2 * ab[(0, 1)] * ab[(0, 2)] * ab[(1, 2)]))
    return val >= -1e-9 * (1 + s[0] * s[1] * s[2]), ('triple', val)
profs = []
for q in [Fr(1), Fr(2), Fr(10), Fr(1000), Fr(10 ** 6)]:
    profs.append(('geo q=%s' % q, [Fr(0)] + [q ** k for k in range(40)]))
for _ in range(per):
    rs = sorted((Fr(rng.randint(1, 80), 10) for _ in range(40)), reverse=True)
    nu = [Fr(0), Fr(1)]
    for x in rs: nu.append(nu[-1] * x)
    profs.append(('rand', nu))
bad_sig = []; bad_cop = []; cnt = 0
for name, nu in profs:
    for l in range(0, lmax + 1):
        for n in range(2, nmax + 1):
            if (l, n) == (0, 2): continue
            N = l + n + 2
            d = [sum(math.comb(i, kk) * nu[kk] for kk in range(i + 1)) for i in range(N + 1)]
            k = coeffs(d, l, n); g = lambda a, b: k.get((a, b), 0)
            cnt += 1
            for key in [(1, 3), (2, 3), (3, 3)]:
                if g(*key) < 0: bad_sig.append((name, l, n, key))
            trade = U * min(g(0, 3), 0)
            A = [[g(0, 0), g(0, 1) / 2, g(0, 2) / 2], [g(0, 1) / 2, g(1, 1), (g(1, 2) + trade) / 2],
                 [g(0, 2) / 2, (g(1, 2) + trade) / 2, g(2, 2)]]
            ok, why = copos3(A)
            if not ok: bad_cop.append((name, l, n, why))
print(f'u={U}: {cnt} (profile, l, n) cases off the corner: negative sigma coefficients {len(bad_sig)} {bad_sig[:4]}; '
      f'non-copositive Q\' {len(bad_cop)} {bad_cop[:4]}')
