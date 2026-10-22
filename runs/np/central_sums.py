"""General (NP) via anti-diagonal certificates. For a profile with Newton coefficients nu_1..nu_D (LC, nu_1 > 0)
kappa_k = sum_n C(k,n) nu_n sum_i C(n-1,i) s_{k-i}  (s = shift sum of rho, s_0 > 0), so kappa_k = sum_r m_r(k) s_{k-r}.
Q_k = kappa_k^2 - kappa_{k-1} kappa_{k+1} is a quadratic form in s. A certificate using only LC differences
s_a s_b - s_{a-1} s_{b+1} (a <= b) and products s_a s_b exists iff on every anti-diagonal a + b = sigma every central
segment sum of coefficients (pairs with a >= a0) is >= 0. Reports the minimum such sum (exact) over random LC nu.
Usage: central_sums.py D Kmax samples seed"""
import sys, random
from fractions import Fraction as F
from math import comb

def m_coeffs(nu, k):
    out = {}
    for n in range(1, len(nu)):
        if n > k: break
        for i in range(n):
            out[i] = out.get(i, 0) + comb(k, n) * nu[n] * comb(n - 1, i)
    return out  # kappa_k = sum_i out[i] * s_{k-i}

def worst(nu, k):
    q = {}
    def add(a, b, v):
        if a < 0 or b < 0: return
        a, b = min(a, b), max(a, b); q[(a, b)] = q.get((a, b), 0) + v
    mk, mm, mp = m_coeffs(nu, k), m_coeffs(nu, k - 1), m_coeffs(nu, k + 1)
    for i, u in mk.items():
        for j, v in mk.items(): add(k - i, k - j, u * v)
    for i, u in mm.items():
        for j, v in mp.items(): add(k - 1 - i, k + 1 - j, -u * v)
    best = None
    for sigma in set(a + b for a, b in q):
        pairs = sorted(((a, b) for (a, b) in q if a + b == sigma), key=lambda p: -p[0])  # from the centre outwards
        tot = 0
        for p in pairs:
            tot += q[p]
            if best is None or tot < best[0]: best = (tot, sigma, p)
    return best

def lc_nu(rng, D):
    ratios = sorted((F(rng.randint(0, 40), 10) for _ in range(D - 1)), reverse=True)
    nu = [F(0), F(rng.randint(1, 20), 10)]
    for r in ratios: nu.append(nu[-1] * r)
    return nu

if __name__ == '__main__':
    D, Kmax, S, rng = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), random.Random(int(sys.argv[4]))
    glob = None
    for _ in range(S):
        nu = lc_nu(rng, D)
        for k in range(2, Kmax + 1):
            w = worst(nu, k)
            if w and (glob is None or w[0] < glob[0]): glob = (w[0], k, w[1], w[2], [str(v) for v in nu])
    print(f'D={D}: minimum central segment sum {float(glob[0]):.4g} at k={glob[1]} sigma={glob[2]} pair={glob[3]} nu={glob[4]}')
