"""Sign of the kernel coefficients omega_{l,a} (Theorem 8.6 recurrence) on the curved-profile linear-ratio family."""
import sys, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from kernel_check import tools
from lfamily import lmember
from probe import linearization, first_negative

def omegas(a_, b, c):
    N = len(c) - 1
    nu, be, f, W, cpol, bpol = tools(b, c)
    apol = lambda i: 1 - bpol(i) - cpol(i)
    res = []
    for k in range(N + 1):
        om = {(0, k): F(1)}
        o = lambda l, a: om.get((l, a), F(0))
        for l in range(0, N):
            for a in range(0, N + 1 - (l + 1)):
                v = apol(l + a) * o(l, a)
                for j in range(0, N + 1):
                    v += (-1) ** j * (W(be, 2*j+1, j, l-j, a+2*j+1) * o(l-j, a+2*j+1)
                                      + W(nu, 2*j+2, j, l-j, a+2*j+2) * o(l-j, a+2*j+2)
                                      + (W(nu, 2*j+2, j+1, l-j-1, a+2*j+2) + W(be, 2*j+2, j+1, l-j-1, a+2*j+2)) * o(l-j-1, a+2*j+2))
                om[(l + 1, a)] = v / cpol(l + 1)
        res.append(om)
    return res

rng = random.Random(3); tot = negmem = 0; worst = None
for trial in range(150):
    N = rng.choice([4, 5, 6, 8])
    a_, b, c = lmember(rng, N, False)
    oms = omegas(a_, b, c); tot += 1
    negs = [(k, key, v) for k, om in enumerate(oms) for key, v in om.items() if v < 0]
    if negs:
        negmem += 1
        if worst is None or min(v for _, _, v in negs) < worst[2]: worst = min(negs, key=lambda t: t[2])
    assert first_negative(linearization(a_, b, c)) is None
print(f'curved L family: {tot} members (all with (P)), {negmem} with some negative kernel coefficient; most negative {worst and (worst[0], worst[1], float(worst[2]))}')
