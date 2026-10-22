import sys
import sympy as sp
from quartic_poly import B, Bp, W4, Dn, LCsub, p, a, x1, x2, x3
def I4b(r2, kB=sp.Rational(1, 2), kP=sp.Rational(1, 2)):
    return (1 - kB)*kP*B(r2, a+2)*Bp(r2-2, a+4)*Dn(r2-1) + (1 - kP)*kB*Bp(r2-1, a+2)*B(r2-2, a+4)*Dn(r2) - W4(r2-2, a+4)*Dn(r2)*Dn(r2-1)
def negcount(e, vars_):
    P = sp.Poly(sp.expand(e.subs(LCsub)), *vars_); return sum(1 for m, c in P.terms() if c < 0), len(P.terms())
for kP in (sp.Rational(1, 2), sp.Rational(1, 4), sp.Rational(3, 4)):
    for r0 in (2, 3, 4, 6, 8):
        n, tot = negcount(I4b(r0 + p, kP=kP), (p, a, x1, x2, x3))
        print(f'kP={kP} r = {r0} + p: {n}/{tot} negative', flush=True)
    for r in range(2, 8):
        n, tot = negcount(I4b(sp.Integer(r), kP=kP), (a, x1, x2, x3))
        print(f'kP={kP} r = {r} exactly: {n}/{tot} negative', flush=True)
