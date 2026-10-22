"""(**') conditional on the set Pi of positions of the (1,1)-steps (type B) in the uniform arrangement of the multiset
(n_y, n_w, n_b) = (2k - c2, 2k - c1, c1 + c2 - 2k). Given Pi, alpha_y(t) ~ Hypergeometric(n_y + n_w, n_y, s_t), s_t = #non-B
among the first t. Box event: i = alpha_y + b_t in [i0, c1-i0], j = s_t - alpha_y + b_t in [j0, c2-j0].
D_Pi = P_k(box | Pi) - P_{k-1}(box | Pi). Reports: min D_Pi, min (D_Pi + D_rev(Pi)), and whether sum_Pi D_Pi equals the
unconditional difference (sanity). Exact. Usage: condB_test.py Kmax"""
import sys, itertools
from fractions import Fraction as F
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def hg_window(N, K, s, lo, hi):  # P(HG(N, K, s) in [lo, hi])
    if s < 0 or s > N: return F(0)
    return F(sum(C(K, a) * C(N - K, s - a) for a in range(max(lo, 0), min(hi, K, s) + 1)), C(N, s))
Kmax = int(sys.argv[1]); worst_single = None; worst_pair = None; bad_sum = 0; cases = 0
for k in range(1, Kmax + 1):
    for c1 in range(k, 2 * k + 1):
        for c2 in range(k, 2 * k + 1):
            ny, nw, nb = 2 * k - c2, 2 * k - c1, c1 + c2 - 2 * k
            if min(ny, nw, nb) < 0: continue
            for i0 in range(0, c1 // 2 + 1):
                for j0 in range(0, c2 // 2 + 1):
                    def prob(t, Pi):
                        b = sum(1 for p in Pi if p < t); s = t - b
                        lo = max(i0 - b, s + b - (c2 - j0)); hi = min(c1 - i0 - b, s + b - j0)
                        return hg_window(ny + nw, ny, s, lo, hi) if lo <= hi else F(0)
                    Ds = {}
                    for Pi in itertools.combinations(range(2 * k), nb):
                        Ds[Pi] = prob(k, Pi) - prob(k - 1, Pi)
                    cases += 1
                    for Pi, v in Ds.items():
                        rev = tuple(sorted(2 * k - 1 - p for p in Pi))
                        pv = v + Ds[rev]
                        if worst_single is None or v < worst_single[0]: worst_single = (v, k, c1, c2, i0, j0, Pi)
                        if worst_pair is None or pv < worst_pair[0]: worst_pair = (pv, k, c1, c2, i0, j0, Pi)
                    tot = sum(Ds.values())
                    if tot < 0: bad_sum += 1
print(f'{cases} boxes; negative total: {bad_sum}')
print('min single D_Pi:', float(worst_single[0]), worst_single[1:])
print('min paired D_Pi + D_rev:', float(worst_pair[0]), worst_pair[1:])
