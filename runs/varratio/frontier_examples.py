"""Exact checks of the ratio-frontier examples quoted in paper.tex (open problems), with clean parameters.
Each: linear profile d_i = i/N, rho_i = r + kappa g(i); checks b nondecreasing, rho_N <= 1, and reports min g(m,N;k)."""
import sys, math
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from rowN_probe import rowN

def check(N, r, kappa, g, label):
    d = [F(i, N) for i in range(N + 1)]
    rho = [r + kappa * g(i, N) for i in range(N + 1)]
    c = [x * y for x, y in zip(rho, d)]; b = [x - y for x, y in zip(d, c)]; a = [1 - x for x in d]
    bmono = all(b[i + 1] >= b[i] for i in range(N)); m, k, v = rowN(a, b, c)
    print(f"{label}: N={N} r={r} kappa={kappa} b nondecreasing={bmono} rho_N<=1={rho[-1] <= 1} min g(m,N;k)={float(v):.3e} at g({m},{N};{k})", flush=True)
    return bmono and v < 0

ex = [
    (48, F(9, 10), F(1, 80), lambda i, N: F(math.comb(i, 3), math.comb(N, 3)), 'binom3'),
    (64, F(9, 10), F(1, 80), lambda i, N: F(i ** 3, N ** 3), 'cube'),
    (40, F(1, 2), F(1, 100), lambda i, N: F(10) ** (i - N), 'exp10'),
    (40, F(1, 2), F(1, 80), lambda i, N: F(int(i == N)), 'top'),
    (120, F(2, 5), F(1, 200), lambda i, N: F(int(i == N)), 'top'),
]
if __name__ == '__main__':
    res = [check(*e) for e in ex]
    print('all fail (P) with b nondecreasing:', all(res))
