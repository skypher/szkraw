"""Does a three-step invariant close the gap?  Invariant omega >= alpha P omega + beta P^2 omega needs, entrywise,
Q <= (alpha(1-alpha) - beta) P^2 + (1 - alpha) beta P^3   (P, Q: positive / negative parts of the merged signed moves).
Test on the curved-profile linear-ratio family over a grid of (alpha, beta)."""
import sys, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from kernel_check import tools
from lfamily import lmember

def PQ(b, c):
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
                    M[((l, a), (lt, at))] = M.get(((l, a), (lt, at)), F(0)) + (-1) ** j * wt / cpol(lt)
    P = {k: v for k, v in M.items() if v > 0}; Q = {k: -v for k, v in M.items() if v < 0}
    return P, Q

def mul(X, Y):
    out = {}
    byfirst = {}
    for (y, z), w in Y.items(): byfirst.setdefault(y, []).append((z, w))
    for (x, y), w1 in X.items():
        for z, w2 in byfirst.get(y, []):
            out[(x, z)] = out.get((x, z), F(0)) + w1 * w2
    return out

rng = random.Random(int(sys.argv[2])); NS = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4, 5, 6, 7, 8]
grid = [(F(1, 2), F(0)), (F(1, 2), F(1, 8)), (F(1, 3), F(2, 9)), (F(2, 5), F(1, 6)), (F(1, 3), F(1, 9))]
viol = {g: 0 for g in grid}; tot = 0; worst = {g: None for g in grid}
for trial in range(int(sys.argv[1])):
    N = rng.choice(NS)
    a_, b, c = lmember(rng, N, False)
    P, Q = PQ(b, c)
    if not Q: continue
    P2 = mul(P, P); P3 = mul(P2, P)
    for key, q in Q.items():
        tot += 1
        for (al, be) in grid:
            rhs = (al * (1 - al) - be) * P2.get(key, F(0)) + (1 - al) * be * P3.get(key, F(0))
            if rhs < q:
                viol[(al, be)] += 1
            r = rhs / q
            if worst[(al, be)] is None or r < worst[(al, be)]: worst[(al, be)] = r
print(f'{tot} negative entries')
for g in grid:
    print(f'alpha={g[0]}, beta={g[1]}: violations {viol[g]}, worst rhs/q = {float(worst[g]) if worst[g] is not None else None}')
