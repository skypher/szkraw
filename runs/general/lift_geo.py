import sys
from fractions import Fraction as F
from lift import check
for N in (3, 4):
    for x in (F(1, 3), F(1, 2), F(2), F(3)):
        sig = [x**k for k in range(N)]
        res = [float(check(N, sig, r, 'rem=max,add=min')) for r in (F(1, 3), F(1))]
        print(f'N={N} geometric x={x}: min entry {res}', flush=True)
