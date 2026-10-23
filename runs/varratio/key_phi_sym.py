"""Symbolic central sums of Phi (cubic in u) for small a. Usage: key_phi_sym.py a"""
import sys, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
a = int(sys.argv[1])
U = sp.symbols('u0:%d' % (a + 2))
P, Lin, Quad, f1, Dc = parts(list(U), a)
Phi = sp.expand(Lin * Dc - f1 * Quad)
poly = sp.Poly(Phi, *P)
q = {}
for m, v in zip(poly.monoms(), poly.coeffs()):
    idx = [i for i, e in enumerate(m) for _ in range(e)]
    q[(idx[0], idx[1])] = sp.expand(v)
for s in range(1, 2 * a + 1):
    tot = 0
    for i in range(s // 2, -1, -1):
        j = s - i
        if j > a: continue
        tot = sp.expand(tot + q.get((i, j), 0))
        if tot != 0:
            print(f'sigma={s} from i={i}: {sp.factor(tot)}')
