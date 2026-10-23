"""Cubic ratios rho = r + t x + tau C(x,2) + sigma C(x,3) with r*sigma <= t*tau (C3, u = 1), on random
log-concave Newton profiles with nondecreasing b. Tests at the corner (l, n) = (0, 2) (exact):
  pointwise quad-B   12 phi2(0) phi2(1) >= 8 c1 phi4(0)
  repaired (1)      (12 phi2(0) + phi3(0)) phi2(1) >= 8 c1 phi4(0)        [consult round 8 claim]
Usage: cubic_corner_repair.py trials seed"""
import sys, math, random
from fractions import Fraction as Fr
T, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
def lc_profile(N):
    while True:
        ratios = sorted((Fr(rng.randint(1, 60), 10) for _ in range(N)), reverse=True)
        nu = [Fr(0), Fr(1)]
        for q in ratios[:N - 1]: nu.append(nu[-1] * q)
        d = [sum(math.comb(i, k) * nu[k] for k in range(i + 1)) for i in range(N + 1)]
        return [x / d[N] for x in d]
cnt = viol_pt = viol_rep = 0; minrep = None
while cnt < T:
    N = rng.randint(4, 10); d = lc_profile(N)
    t = Fr(rng.randint(0, 50), 10 ** rng.randint(1, 4)); tau = Fr(rng.randint(0, 50), 10 ** rng.randint(1, 5))
    r = Fr(rng.randint(1, 99), 100)
    sig = Fr(rng.randint(0, 50), 10 ** rng.randint(0, 4))
    if r * sig > t * tau: continue
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    if any(b[i] > b[i + 1] for i in range(N)): continue
    D = lambda n, l: sum((-1) ** (n - i) * math.comb(n, i) * c[l + i] for i in range(n + 1))
    cnt += 1
    pt = 12 * D(2, 0) * D(2, 1) - 8 * c[1] * D(4, 0)
    rep = (12 * D(2, 0) + D(3, 0)) * D(2, 1) - 8 * c[1] * D(4, 0)
    viol_pt += pt < 0; viol_rep += rep < 0
    if 8 * c[1] * D(4, 0) > 0:
        q = (12 * D(2, 0) + D(3, 0)) * D(2, 1) / (8 * c[1] * D(4, 0))
        if minrep is None or q < minrep: minrep = q
print(f"{cnt} admissible cubic arrays: pointwise corner fails {viol_pt}, repaired corner fails {viol_rep}, "
      f"min repaired ratio {float(minrep):.4f}")
