"""Signed domination test: merge all moves between the same pair of nodes into one signed contribution
(-1)^j * weight / c(dest), split into P (positive) and Q (|negative|), test P^2 >= 4Q entrywise.
Applied to the curved-profile linear-ratio family L, and to criterion S as control."""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from kernel_check import tools
from lfamily import lmember
import stoch

def signed_check(b, c):
    N = len(c) - 1
    nu, be, f, W, cpol, bpol = tools(b, c)
    dn = [x + y for x, y in zip(nu, be)]
    M = {}
    for l in range(N + 1):
        for a in range(N + 1 - l):
            for j in range(N + 1):
                for wt, (dl, da) in ((W(be, 2*j+1, j, l, a), (j+1, -(2*j+1))), (W(nu, 2*j+2, j, l, a), (j+1, -(2*j+2))),
                                     (W(dn, 2*j+2, j+1, l, a), (j+2, -(2*j+2)))):
                    lt, at = l + dl, a + da
                    if at < 0 or lt + at > N or wt == 0: continue
                    key = ((l, a), (lt, at))
                    M[key] = M.get(key, F(0)) + (-1) ** j * wt / cpol(lt)
    P = {k: v for k, v in M.items() if v > 0}; Q = {k: -v for k, v in M.items() if v < 0}
    P2 = {}
    for (x, y), w1 in P.items():
        for (y2, z), w2 in P.items():
            if y2 == y: P2[(x, z)] = P2.get((x, z), F(0)) + w1 * w2
    viol = [k for k, q in Q.items() if P2.get(k, F(0)) < 4 * q]
    ratio = min((P2.get(k, F(0)) / q for k, q in Q.items()), default=None)
    return len(Q), len(viol), ratio

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[2])); per = int(sys.argv[1])
    for name, gen in (('L curved', lambda N: lmember(rng, N, False)), ('S (w noninc)', lambda N: stoch.member(rng, N, 'M'))):
        tq = tv = 0; worst = None
        for N in (4, 5, 6, 8, 10):
            for _ in range(per):
                a_, b, c = gen(N)
                nq, nv, ratio = signed_check(b, c)
                tq += nq; tv += nv
                if ratio is not None and (worst is None or ratio < worst): worst = ratio
        print(f'{name}: {tq} negative entries, {tv} with P^2 < 4Q; worst P^2/Q ratio {float(worst) if worst is not None else None}', flush=True)
