"""Far-field check of the blockwise lemmas at larger a: M_{0,sigma} for sigma >= 2, and S_{2,0} = M_11 + M_{0,2},
on geometric u (u0 = 1/w) with tiny w, a <= amax (exact). Usage: key_M0_far.py amax"""
import sys, math
from fractions import Fraction as Fr
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_S_low import pieces
C = math.comb
amax = int(sys.argv[1]); res = {}
for a in range(3, amax + 1):
    for w in [Fr(1, 10), Fr(1, 100), Fr(1, 1000), Fr(1, 10 ** 6)]:
        u = [1 / w, Fr(1)] + [w ** (n - 1) for n in range(2, amax + 5)]
        M = pieces(u, a)
        for s in range(2, a + 1):
            v = M(0, s)
            if v < 0: res.setdefault(('M0', s), []).append((a, float(w)))
        S20 = M(1, 1) + M(0, 2)
        if S20 < 0: res.setdefault(('S20', 2), []).append((a, float(w)))
for k, v in sorted(res.items()): print(k, 'negative at (a, w):', v[:8], '...' if len(v) > 8 else '')
if not res: print('no negative values')
