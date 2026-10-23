"""Sharpness probe at r = 1. Constant-ratio array a = 1 - d, b = (1-r) d, c = r d, profile d_i = D(i)/D(N),
D(i) = sum_k C(i,k) s_k (Newton coefficients s_1..s_N of the profile). For N odd the corner g(N,N;N) vanishes at
r = 1 (parity), so (P) near r = 1 needs g1 = -dg/dr at r = 1 to be >= 0. Prints g1 symbolically in s (sympy),
factored. Usage: corner_r1.py N"""
import sys
import sympy as sp
N = int(sys.argv[1])
s = sp.symbols(f's1:{N+1}', positive=True); eta = sp.Symbol('eta')
D = [sum(sp.binomial(i, k) * s[k - 1] for k in range(1, i + 1)) for i in range(N + 1)]
d = [x / D[N] for x in D]
r = 1 - eta
a = [1 - x for x in d]; b = [(1 - r) * x for x in d]; c = [r * x for x in d]
size = N + 1
def trunc(e):  # keep terms up to eta^1
    e = sp.expand(e)
    return e.coeff(eta, 0) + eta * e.coeff(eta, 1)
cur = [[sp.Integer(int(i == j)) for j in range(size)] for i in range(size)]; prev = [[sp.Integer(0)] * size for _ in range(size)]
for m in range(N):
    nxt = [[sp.Integer(0)] * size for _ in range(size)]
    for i in range(size):
        for j in range(size):
            v = (b[i] - b[m]) * cur[i][j] - c[m] * prev[i][j]
            if i: v += c[i] * cur[i - 1][j]
            if i < N: v += a[i] * cur[i + 1][j]
            nxt[i][j] = trunc(sp.together(v / a[m]))
    prev, cur = cur, nxt
g = sp.expand(cur[N][N])
g0, g1 = sp.factor(g.coeff(eta, 0)), sp.factor(g.coeff(eta, 1))
print('g0 =', g0)
print('g1 =', g1)
