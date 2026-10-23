"""Phi3loc (E3 weight 0) >= 0 at the endpoints z = 0 and z = 1/q via per-index coefficient inequalities (u_1 = 1).
Linearize the products with u_i u_j >= u_{i+j-1}: YJ >= sum_k c_k u_k, c_k = sum_{i+j=k+1, i>=2, 2<=j<=a-1} C(a,i)C(a-1,j).
z = 0:   need_k <= avail_k with avail_k = kap' C(a,k) + s c_k, need_k = 4(k-2)(C(a,3) - C(k,3)) C(a,k)  (3 <= k <= a).
z = 1/q: Phi q/(1+q) = (sY + 2C(a,3))Y'/(1+q) + Y(sJ + kap') - (4s/q)H* - 4T3; with 2C(a,3)Y'/(1+q) >= (2C(a,3)/q) sum C(a-1,n-1)u_n,
  sY Y'/(1+q) >= s C(a,2) sum_{n>=3} C(a-1,n-1) u_n, and u_n/q <= u_{n-1}:
  u_2: kap' C(a,2) - 2 s C(a,3) = s C(a,2)/3 >= 0;
  k >= 3: avail_k = kap' C(a,k) + s c_k + s C(a,2) C(a-1,k-1), need_k = 4(k-2)(C(a,3)-C(k,3))C(a,k) + s(10(k+1)/3 - 8) C(a,k+1).
Reports the worst ratio avail/need per a, with exact c_k and with the two-product bound c_k >= C(a,2)C(a-1,k-1) + [k>=4] C(a,k-1)C(a-1,2).
Usage: phi3loc_perk.py amax"""
import sys
from fractions import Fraction as F
from math import comb as C
amax = int(sys.argv[1])
def ck(a, k, mode):
    if mode == 'exact':
        return sum(C(a, i) * C(a - 1, k + 1 - i) for i in range(2, a + 1) if 2 <= k + 1 - i <= a - 1)
    v = C(a, 2) * C(a - 1, k - 1)
    if k >= 4: v += C(a, k - 1) * C(a - 1, 2)
    return v
for mode in ('exact', 'two'):
    worst = []
    for a in range(3, amax + 1):
        s = C(a - 1, 2); kp = F(s * (2 * a - 3), 3)
        assert kp * C(a, 2) - 2 * s * C(a, 3) == F(s * C(a, 2), 3)
        wa = None
        for k in range(3, a + 1):
            c = ck(a, k, mode)
            av0 = kp * C(a, k) + s * c; nd0 = 4 * (k - 2) * (C(a, 3) - C(k, 3)) * C(a, k)
            av1 = av0 + s * C(a, 2) * C(a - 1, k - 1); nd1 = nd0 + s * (F(10 * (k + 1), 3) - 8) * C(a, k + 1)
            for tag, av, nd in (('z0', av0, nd0), ('z1/q', av1, nd1)):
                if nd > 0:
                    r = av / nd
                    if wa is None or r < wa[0]: wa = (r, tag, k)
        if wa: worst.append((float(wa[0]), a, wa[1], wa[2]))
    worst.sort()
    print(mode, 'worst 6 (ratio avail/need, a, endpoint, k):', [(round(x[0], 4),) + x[1:] for x in worst[:6]])
    print(mode, 'any ratio < 1:', [x for x in worst if x[0] < 1][:10])
