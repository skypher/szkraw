"""Certificate search for degree-3 (NP): Q = k^2 e_k^2 - (k^2-1) e_{k-1} e_{k+1} as a nonnegative combination of
LC differences D(i,j) = x_i x_j - x_{i-1} x_{j+1} (1 <= i <= j <= 3) and products x_i x_j, in x = (s_{k-3},...,s_{k+1}).
LP feasibility at sample points (nu1, nu2, nu3 with nu2^2 >= nu1 nu3, k >= 2). Usage: deg3_lp.py samples seed"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
import sympy as sp

x = sp.symbols('x0:5'); n1, n2, n3, k = sp.symbols('n1 n2 n3 k')
A = lambda kk: n1 + (kk - 1) * n2 / 2 + (kk - 1) * (kk - 2) * n3 / 6
B = lambda kk: (kk - 1) * n2 / 2 + (kk - 1) * (kk - 2) * n3 / 3
C = lambda kk: (kk - 1) * (kk - 2) * n3 / 6
ek = A(k) * x[3] + B(k) * x[2] + C(k) * x[1]
ekm = A(k - 1) * x[2] + B(k - 1) * x[1] + C(k - 1) * x[0]
ekp = A(k + 1) * x[4] + B(k + 1) * x[3] + C(k + 1) * x[2]
Q = sp.expand(k ** 2 * ek ** 2 - (k ** 2 - 1) * ekm * ekp)
mons = [(i, j) for i in range(5) for j in range(i, 5)]
gens = [('D', i, j) for i in range(1, 4) for j in range(i, 4)] + [('P', i, j) for (i, j) in mons]
def gpoly(g):
    if g[0] == 'D': return x[g[1]] * x[g[2]] - x[g[1] - 1] * x[g[2] + 1]
    return x[g[1]] * x[g[2]]
G = np.array([[float(sp.Poly(gpoly(g), *x).coeff_monomial(x[i] * x[j])) for g in gens] for (i, j) in mons])
Qp = sp.Poly(Q, *x)
def feasible(vals):
    qv = np.array([float(Qp.coeff_monomial(x[i] * x[j]).subs(vals)) for (i, j) in mons])
    res = linprog(np.zeros(len(gens)), A_eq=G, b_eq=qv, bounds=[(0, None)] * len(gens), method='highs')
    return res.status == 0, res
if __name__ == '__main__':
    S, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
    bad = 0
    for _ in range(S):
        a1 = rng.uniform(0.01, 5); a2 = rng.uniform(0, 5); a3 = a2 * a2 / a1 * rng.choice([0, rng.random(), 1])
        kk = rng.choice([2, 3, 4, 5, 7, 10, 20])
        ok, res = feasible({n1: a1, n2: a2, n3: a3, k: kk})
        if not ok:
            bad += 1
            if bad <= 5: print('infeasible at nu =', (round(a1, 3), round(a2, 3), round(a3, 3)), 'k =', kk)
    print(f'{bad}/{S} sample points without a certificate of this form')
