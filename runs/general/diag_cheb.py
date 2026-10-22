"""t^0 layer (r = 1) of the D recursion, unrolled along the diagonal:
D_{m,n} = sum_j W_j c_j (+ nonnegative base terms), c_j = phi(n-j) - phi(m-j),
W_j = [prod_{i<j} d_{n-i}/a_{m-1-i}] H_{m-1-j,n-j} / a_{m-1-j}  (t^0 coefficients).
Checks, over deep triples with a negative c_0: (a) c_j nondecreasing in j; (b) W_j nondecreasing in j; (c) sum_j c_j >= 0;
(d) the Chebyshev bound sum c_j W_j >= (1/J) sum c_j sum W_j. Reports violations."""
import sys
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables
from corner_bern_num import profile
def run(d, label):
    N = len(d) - 1; a = [1 - x for x in d]; H, Dt = tables(d)
    phi = [None] + [d[i]*a[i-1] for i in range(1, N+1)]
    h0 = lambda i, j, k: (H[i][j][k][0] if H[i][j][k] else F(0))
    stats = {'cases': 0, 'c_mono': 0, 'W_mono': 0, 'sum_c': 0, 'D_pos': 0}
    for (m, n, k), Dp in Dt.items():
        if m < 2 or phi[n] >= phi[m]: continue
        cs = []; Ws = []; w = F(1)
        for j in range(m):
            cs.append(phi[n-j] - phi[m-j]); Ws.append(w*h0(m-1-j, n-j, k)/a[m-1-j])
            w *= d[n-j]/a[m-1-j]
        if all(x == 0 for x in Ws): continue
        stats['cases'] += 1
        stats['c_mono'] += all(cs[i+1] >= cs[i] for i in range(len(cs)-1))
        nz = [i for i, x in enumerate(Ws) if x != 0]
        Wn = [Ws[i] for i in nz]
        stats['W_mono'] += all(Wn[i+1] >= Wn[i] for i in range(len(Wn)-1))
        stats['sum_c'] += sum(cs[i] for i in nz) >= 0
        stats['D_pos'] += (Dp[0] if Dp else 0) >= 0
    print(f'{label}: {stats}', flush=True)
for N in (6, 8, 10):
    run(profile(N, [F(0)]*(N-1)), f'Krawtchouk N={N}')
    run(profile(N, [F(1, 5)]*(N-1)), f'geom x=1/5 N={N}')
    run(profile(N, [F(1, 2), F(1, 4)] + [F(1, 8)]*(N-3)), f'LC two-level N={N}')
