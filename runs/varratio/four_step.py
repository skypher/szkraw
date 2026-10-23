"""Invariant omega >= a1 P omega + a2 P^2 omega + a3 P^3 omega propagates if, entrywise,
Q <= (a1(1-a1) - a2) P^2 + ((1-a1) a2 - a3) P^3 + (1-a1) a3 P^4.
Report worst margin for several (a1, a2, a3) on the curved-profile linear-ratio family."""
import sys, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from lfamily import lmember
from three_step import PQ, mul
rng = random.Random(int(sys.argv[2])); NS = [int(x) for x in sys.argv[3].split(',')]
grid = [(F(1,2), F(1,8), F(0)), (F(1,2), F(1,8), F(1,64)), (F(1,2), F(3,32), F(1,64)), (F(1,2), F(1,10), F(1,40)),
        (F(3,5), F(1,10), F(1,50)), (F(1,2), F(1,12), F(1,48))]
worst = {g: None for g in grid}; viol = {g: 0 for g in grid}; tot = 0
for t in range(int(sys.argv[1])):
    N = rng.choice(NS)
    a_, b, c = lmember(rng, N, False)
    P, Q = PQ(b, c)
    if not Q: continue
    P2 = mul(P, P); P3 = mul(P2, P); P4 = mul(P3, P)
    for k, q in Q.items():
        tot += 1
        for g in grid:
            a1, a2, a3 = g
            rhs = (a1*(1-a1) - a2)*P2.get(k, F(0)) + ((1-a1)*a2 - a3)*P3.get(k, F(0)) + (1-a1)*a3*P4.get(k, F(0))
            if rhs < q: viol[g] += 1
            r = rhs / q
            if worst[g] is None or r < worst[g]: worst[g] = r
print(f'{tot} negative entries')
for g in grid: print(f'{tuple(str(x) for x in g)}: violations {viol[g]}, worst margin {float(worst[g]):.4f}')
