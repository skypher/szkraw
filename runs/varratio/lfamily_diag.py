"""Which kernel moves go negative on the curved-profile linear-ratio family, and where."""
import sys, math, random
from fractions import Fraction as F
from collections import Counter
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from kernel_check import tools
from lfamily import lmember
rng = random.Random(7); cnt = Counter(); members = 0; negm = 0
for trial in range(200):
    N = rng.choice([4, 5, 6, 8])
    a_, b, c = lmember(rng, N, False)
    nu, be, f, W, cpol, bpol = tools(b, c)
    dn = [x + y for x, y in zip(nu, be)]
    bad = False
    for l in range(N + 1):
        for a in range(N + 1 - l):
            for j in range(N + 1):
                for typ, wt, (dl, da) in (('A', W(be, 2*j+1, j, l, a), (j+1, -(2*j+1))), ('B', W(nu, 2*j+2, j, l, a), (j+1, -(2*j+2))),
                                          ('C', W(dn, 2*j+2, j+1, l, a), (j+2, -(2*j+2)))):
                    lt, at = l + dl, a + da
                    if at < 0 or lt + at > N: continue
                    if wt < 0: cnt[(typ, j)] += 1; bad = True
    members += 1; negm += bad
print(f'{members} members, {negm} with a negative move; negative moves by (type, j): {dict(cnt)}')
# Newton coefficient signs
rng = random.Random(8); sg = Counter()
for trial in range(200):
    N = rng.choice([5, 6, 8])
    a_, b, c = lmember(rng, N, False)
    from mixed import newton_coeffs
    beta = newton_coeffs(b); kap = newton_coeffs(c); dl = [x + y for x, y in zip(beta, kap)]
    sg['beta_k<0 some k>=3'] += any(x < 0 for x in beta[3:]); sg['kappa_k<0 some k'] += any(x < 0 for x in kap[1:])
    sg['delta_k<0 some k'] += any(x < 0 for x in dl[1:]); sg['b nondecr'] += all(b[i+1] >= b[i] for i in range(N))
print(dict(sg), 'of 200')
