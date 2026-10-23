"""Sign structure of w^2*L_k(1/w) (w = u_2, u_1 = 1, u_0 = 1/w) as a polynomial in u_2..u_{a+1}, for small a and k.
Prints monomials with negative coefficients."""
import sys, math
import sympy as sp
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_extreme import L
from fractions import Fraction as F
a, k = int(sys.argv[1]), int(sys.argv[2])
us = sp.symbols('u2:%d' % (a + 3)); w = us[0]
u = [1 / w, sp.Integer(1)] + list(us)
s = [sp.Integer(math.comb(i, k)) for i in range(a)]
expr = sp.expand(sp.cancel(L(u, a, s[a - 1] / w, s, sp.Integer(2)) * w ** 2))
P = sp.Poly(expr, *us)
neg = [(m, c) for m, c in zip(P.monoms(), P.coeffs()) if c < 0]
pos = [(m, c) for m, c in zip(P.monoms(), P.coeffs()) if c > 0]
fmt = lambda m: '*'.join(f'u{i+2}^{e}' if e > 1 else f'u{i+2}' for i, e in enumerate(m) if e) or '1'
print(f'a={a} k={k}: {len(pos)} positive, {len(neg)} negative monomials')
for m, c in neg: print('  NEG', fmt(m), c)
