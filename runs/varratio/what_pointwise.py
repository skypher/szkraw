"""Exact check of the pointwise W-hat bound for conjecture (G):
phi_2(l) * what_n(l+1) >= c_{l+1} * sum_j theta_{n,j} w^{(j)}_{n+2}(l), j = 2..n+2, with
theta_{n,2} = C(n,2)/C(n+2,2); theta_{n,j} = 1 - j(j-1)/((n+1)(n+2)) for 3 <= j <= n; theta_{n,n+1} = 2/(n+2); theta_{n,n+2} = 1,
w^{(j)}_m(l) = C(m,j) D^j rho(l+m-j) f_{m-j}(l). Then the summed detour quotient theta * m(m-1)J/(2(m-J-1)) >= 2 is checked too.
Usage: what_pointwise.py Ns per seed"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from g_ingredients import member
Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
bad = 0; checks = 0; minq = None
for N in Ns:
    for it in range(per):
        d, co = member(rng, N, ['mix', 'steep', 'lin'][it % 3])
        rhof = lambda x: sum(ck * math.comb(x, k) for k, ck in enumerate(co) if k <= x)
        rv = [rhof(i) for i in range(3 * N + 5)]
        dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
        c = [rv[i] * d[i] for i in range(N + 1)]
        f = lambda n, l: dif(d, n, l); phi = lambda n, l: dif(c, n, l)
        wj = lambda j, m, l: math.comb(m, j) * dif(rv, j, l + m - j) * f(m - j, l)
        what = lambda n, l: sum(wj(j, n, l) for j in range(2, n + 1))
        for l in range(N - 1):
            for n in range(2, N - l - 1):
                th = {2: F(math.comb(n, 2), math.comb(n + 2, 2)), n + 1: F(2, n + 2), n + 2: F(1)}
                for j in range(3, n + 1): th[j] = 1 - F(j * (j - 1), (n + 1) * (n + 2))
                lhs = phi(2, l) * what(n, l + 1); rhs = c[l + 1] * sum(th[j] * wj(j, n + 2, l) for j in range(2, n + 3))
                checks += 1
                if lhs < rhs: bad += 1
for J in range(2, 40):
    for m in range(2 * J + 1, 200):
        n = m - 2
        for j in range(2, n + 3):
            th = F(math.comb(n, 2), math.comb(n + 2, 2)) if j == 2 else (F(2, n + 2) if j == n + 1 else (F(1) if j == n + 2 else 1 - F(j * (j - 1), (n + 1) * (n + 2))))
            q = th * F(m * (m - 1) * J, 2 * (m - J - 1))
            if minq is None or q < minq[0]: minq = (q, J, m, j)
print(f'{checks} pointwise checks, {bad} failures; minimum summed quotient {float(minq[0]):.4f} at J={minq[1]}, m={minq[2]}, j={minq[3]}')
