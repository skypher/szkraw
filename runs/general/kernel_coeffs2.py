import random
from fractions import Fraction as F
from kernel_coeffs import kernel_min
rng = random.Random(9)
def lc_sig(N, rho): s = [F(1)]; [s.append(s[-1]*x) for x in rho]; return s
for N in (6, 8, 10):
    cases = [('geometric x=1/5', lc_sig(N, [F(1, 5)]*(N-1))), ('geometric x=2', lc_sig(N, [F(2)]*(N-1))),
             ('LC random', lc_sig(N, sorted([F(rng.randint(0, 30), 10) for _ in range(N-1)], reverse=True))),
             ('LC random 2', lc_sig(N, sorted([F(rng.randint(0, 30), 10) for _ in range(N-1)], reverse=True))),
             ('log-convex random', lc_sig(N, sorted([F(rng.randint(1, 30), 10) for _ in range(N-1)]))),
             ('log-convex steep', lc_sig(N, [F(i+1, 4) for i in range(N-1)]))]
    for name, sig in cases:
        wv, wh = kernel_min(sig, N)
        print(f'N={N} {name:18s}: min A_r c = {float(wv):.3e} at (k,r,a)={wh}', flush=True)
