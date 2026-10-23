"""Polarization of the weighted B-detour for cubic ratios (exact).
D(l,n) = (n+1)(n+2) phi_2(l) phi_n(l+1) - 8(n-1) c_{l+1} phi_{n+2}(l) is a quadratic form in the ratio's Newton
coefficients rho = (r, t, tau, sigma): D = sum_{a<=b} k_ab rho_a rho_b. For each profile and (l, n), compute k_ab and
report: negative coefficients (by pair), and the margins needed under r sigma <= t tau:
  (i) k_rs + k_tt? no: k_rs + k_(t,tau) >= 0 when k_rs < 0 (trade r sigma <= t tau),
  (ii) whether the sigma-free part (quadratic case) is >= 0 coefficientwise or only jointly.
Profiles: random LC Newton sequences and geometric nu_k = q^k with large q (far field). Usage: cubic_quadB_polar.py per seed"""
import sys, math, random
from fractions import Fraction as Fr
names = ['r', 't', 'tau', 'sig']
def basis(i, a):  # value of the a-th basis ratio at i
    return [1, i, math.comb(i, 2), math.comb(i, 3)][a]
def coeffs(d, l, n):
    N = len(d) - 1
    D = lambda seq, k, x: sum((-1) ** (k - i) * math.comb(k, i) * seq[x + i] for i in range(k + 1))
    cs = [[basis(i, a) * d[i] for i in range(N + 1)] for a in range(4)]
    K, L = (n + 1) * (n + 2), 8 * (n - 1)
    k = {}
    for a in range(4):
        for b in range(4):
            v = K * D(cs[a], 2, l) * D(cs[b], n, l + 1) - L * cs[a][l + 1] * D(cs[b], n + 2, l)
            key = (min(a, b), max(a, b)); k[key] = k.get(key, 0) + v
    return k
if __name__ == '__main__':
    per, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
    def profiles():
        out = []
        for q in [Fr(1), Fr(3), Fr(10), Fr(100), Fr(10 ** 4)]:
            out.append(('geo q=%s' % q, [Fr(0)] + [q ** k for k in range(40)]))
        for _ in range(per):
            rs = sorted((Fr(rng.randint(1, 80), 10) for _ in range(40)), reverse=True)
            nu = [Fr(0), Fr(1)]
            for x in rs: nu.append(nu[-1] * x)
            out.append(('rand', nu))
        return out
    negs = {}; worst_trade = None; quad_bad = 0; corner = []
    for name, nu in profiles():
        for l in range(0, 8):
            for n in range(2, 9):
                N = l + n + 2
                d = [sum(math.comb(i, kk) * nu[kk] for kk in range(i + 1)) for i in range(N + 1)]
                k = coeffs(d, l, n)
                for key, v in k.items():
                    if v < 0:
                        negs.setdefault(key, 0); negs[key] += 1
                krs, ktt = k.get((0, 3), 0), k.get((1, 2), 0)
                if krs < 0:
                    m = (krs + ktt) / (-krs)
                    if worst_trade is None or m < worst_trade[0]: worst_trade = (m, name, l, n)
                if k.get((1, 3), 0) < 0: corner.append((name, l, n, float(k[(1, 3)])))
    print('negative coefficients by pair (counts):', {f'{names[a]}*{names[b]}': c for (a, b), c in sorted(negs.items())})
    print('worst (k_rs + k_ttau)/|k_rs| when k_rs < 0:', (float(worst_trade[0]),) + worst_trade[1:] if worst_trade else None)
    print('negative t*sigma coefficient at (profile, l, n):', corner[:12], '... total', len(corner))
