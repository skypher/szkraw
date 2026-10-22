"""Exact checks of the round-2 consult claims (reviews/consult-D-answer.md)."""
from fractions import Fraction as F
from math import comb
from gamma_check import tables
from corner_bern_num import profile
def Dpoly(d, m, n, k):
    H, Dt = tables(d); return Dt[(m, n, k)]
# (a) increment-LC counterexample
d = [F(x, 7) for x in (0, 1, 3, 5, 7)]
print('d=(0,1,3,5,7)/7: D_{3,4}^4 =', [str(c) for c in Dpoly(d, 3, 4, 4)], ' expected (4t^2-1)/84 ->', [str(F(-1, 84)), '0', str(F(4, 84))])
# (b) control
d = [F(x, 121) for x in (0, 30, 60, 90, 121)]
print('control: [t^0] D_{3,4}^4 =', Dpoly(d, 3, 4, 4)[0], ' expected', F(-809, 671671))
# (c) identity (4)/(6) and (10) on LC profiles
def t0_formula(d):
    N = len(d) - 1; a = [1 - x for x in d]; phi = [None] + [d[i]*a[i-1] for i in range(1, N+1)]
    return ((phi[N] - phi[3])*(phi[N] - phi[1]) + phi[N]*(phi[N-1] - phi[2]))/(a[1]*a[2])
def t0_minor(s, N):
    A, B, C = s[1], s[2], s[3]
    Fi = lambda i: sum(comb(i, j)*s[j] for j in range(1, i+1)); T = Fi(N)
    U = sum(comb(N, j)*s[j] for j in range(2, N+1)); V = sum(comb(N-1, j-1)*s[j] for j in range(2, N+1)); W = sum(comb(N-2, j-1)*s[j] for j in range(2, N+1))
    c = lambda j: (j - 3)*comb(N-1, j-1)
    L = sum(c(j)*s[j] for j in range(4, N+1)); M = sum(c(j)*s[j-1] for j in range(4, N+1))
    Q = (N-2)*V*(2*V + W - 4*B - C) - U*(V - W + B) + 2*B*V
    R = V*(U*(2*V + W - 4*B - C) - V*(V + W) + 3*B*B + B*C)
    return (-A*A*L + A*Q + R)/(T*(T - A)*(T - 2*A - B))
import random
rng = random.Random(3); bad = 0; tot = 0
for N in (4, 5, 6, 8, 10, 12):
    for _ in range(6):
        rho = sorted([F(rng.randint(0, 30), 10) for _ in range(N-1)], reverse=True)
        s = [F(0), F(1)]
        for k in range(2, N+1): s.append(s[-1]*rho[k-2])
        d = profile(N, rho); D = Dpoly(d, 3, N, N); tot += 1
        ok = D[0] == t0_formula(d) == t0_minor(s, N) and all(c >= 0 for c in D)
        bad += not ok
print(f'identity (4) = (6) = [t^0] D_(3,N)^N and D_(3,N)^N >= 0: {tot} LC profiles N = 4..12, {bad} mismatches')
for N in (4, 6, 9):
    A, B = F(1), F(1, 3); s = [F(0), A, B] + [F(0)]*(N-2)
    T = N*A + comb(N, 2)*B
    f10 = F(3, 2)*B*B*(2*A + N*B)*(N-1)*(N-2)*(N-3)/(T*(T - A)*(T - 2*A - B))
    d = profile(N, [B] + [F(0)]*(N-2))
    print(f'(10) at N={N}:', Dpoly(d, 3, N, N)[0] == f10)
# (d) geometric (D) all triples
for N in (5, 8):
    for x in (F(1, 7), F(2)):
        H, Dt = tables(profile(N, [x]*(N-1)))
        print(f'geometric x={x} N={N}: D failures', sum(1 for p in Dt.values() if any(c < 0 for c in p)))
