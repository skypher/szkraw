"""Exact test: edge u_1-linearization of A and B (runs/lean_plan/phi3_test.py), as for the forms of Theorem 8.16.
x*y >= u_1 * sum_n edgeCoef(x,y)_n u_n for x, y with x_0 = y_0 = 0 (GenEdge.lean); u_0 * h -> handled by
u_0 u_{n+1} <= u_1 u_n where needed. A = s*Y*X'' - C(a-1,3) u_1 Y - 4 u_1 T3 + u_1 E3^0 (E3^0 >= 0 kept);
B = s*(X*Y' + Y*X'') - 4 s u_1 H* - 4 s u_1 Hsh + u_1*(-C(a,3) Y' - C(a-1,3) Y - 4 T3 + E3^0 + C(a,3) u_1) + C(a,3) u_0 u_1.
Prints, per a, the indices n with e_n < 0. Usage: phi3_edge.py amax"""
import sys
from fractions import Fraction as F
from math import comb as C
amax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
def run(a):
    R = range(a + 4)
    s = C(a - 1, 2)
    Z = lambda: {n: 0 for n in R}
    X = Z(); Xpp = Z(); Y = Z(); Yp = Z(); Hs = Z(); Hsh = Z(); T3 = Z(); E3 = Z()
    for n in range(1, a + 1): X[n] = C(a, n)
    for n in range(1, a): Xpp[n] = C(a - 1, n) - (1 if n == 1 else 0)
    for n in range(2, a + 1): Y[n] = C(a, n)
    for n in range(2, a):
        Yp[n] += C(a - 1, n); Yp[n + 1] += C(a - 1, n)
    for n in range(3, a + 1):
        Hs[n] = (n - 2) * C(a, n); Hsh[n - 1] += (n - 2) * C(a, n)
        T3[n] = (n - 2) * C(a, n) * (C(a, 3) - C(n, 3))
        w = (n - 2) * C(a, n) * C(n, 3)
        E3[n - 1] += 3 * w; E3[n - 2] += 3 * w
        if n - 3 >= 1: E3[n - 3] += w
    def edge(x, y):
        out = Z()
        for n in R:
            v = x[1] * y[n] + x[2] * (y[n - 1] if n >= 1 else 0)
            if n >= 3: v += y[1] * x[n]
            if n >= 4: v += y[2] * x[n - 1]
            out[n] = v
        return out
    eYX = edge(Y, Xpp); eXY = edge(X, Yp)
    eA = {n: s * eYX[n] - C(a - 1, 3) * Y[n] - 4 * T3[n] + E3[n] for n in R}
    eB = {n: s * (eXY[n] + eYX[n]) - 4 * s * Hs[n] - 4 * s * Hsh[n] - C(a, 3) * Yp[n] - C(a - 1, 3) * Y[n]
          - 4 * T3[n] + E3[n] + (C(a, 3) if n == 1 else 0) for n in R}
    return eA, eB
def bad(a):
    eA, eB = run(a)
    return [n for n in eA if eA[n] < 0], [n for n in eB if eB[n] < 0]
if __name__ == '__main__':
  for a in range(3, amax + 1):
    ba, bb = bad(a)
    if ba or bb: print(f'a={a}: A neg at {ba}, B neg at {bb}')
  print('done')
