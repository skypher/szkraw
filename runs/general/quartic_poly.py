"""Coefficient test of the quartic local inequalities (kappa = 1/2) in LC coordinates:
s2 = rho1, s3 = rho1 rho2, s4 = rho1 rho2 rho3, rho1 = x1+x2+x3, rho2 = x2+x3, rho3 = x3; r = r0 + p (p >= 0)."""
import sympy as sp
from cubic_symbolic import G
a_, r_, t_ = sp.symbols('a r t'); s2, s3, s4 = sp.symbols('s2 s3 s4')
p, a, x1, x2, x3 = sp.symbols('p a x1 x2 x3', nonnegative=True)
g = G(4, [sp.Integer(1), s2, s3, s4])
rho1, rho2, rho3 = x1 + x2 + x3, x2 + x3, x3
LCsub = {s2: rho1, s3: rho1*rho2, s4: rho1*rho2*rho3}
def F(key, rr, aa, div_t=False):
    e = g[key]/t_ if div_t else g[key]
    return sp.expand(e.subs({r_: rr, a_: aa}))
Dn = lambda n: n + n*(n-1)/2*s2 + n*(n-1)*(n-2)/6*s3 + n*(n-1)*(n-2)*(n-3)/24*s4
A = lambda rr, aa: F((-1, 0), rr, aa, True); B = lambda rr, aa: F((-2, 0), rr, aa); Bp = lambda rr, aa: F((-2, 1), rr, aa)
W3 = lambda rr, aa: -F((-3, 1), rr, aa, True); W4 = lambda rr, aa: -F((-4, 1), rr, aa)
def test(name, expr, r0, lc=True):
    e = expr.subs({r_: r0 + p}) if False else expr
    e = sp.expand(e.subs(LCsub) if lc else e)
    P = sp.Poly(e, *( (p, a, x1, x2, x3) if lc else (p, a, s2, s3, s4) ))
    neg = [(m, c) for m, c in P.terms() if c < 0]
    print(f'{name} ({"LC coords" if lc else "raw sigma"}): {len(P.terms())} terms, {len(neg)} negative' + (f', e.g. {neg[:4]}' if neg else ''), flush=True)
    return neg
r = 1 + p
I3 = sp.Rational(1, 4)*(A(r, a+1)*B(r-1, a+3) + B(r, a+2)*A(r-1, a+3)) - Dn(r)*W3(r-1, a+3)
I4a = sp.Rational(1, 4)*B(r, a+2)*B(r-1, a+4) - Dn(r)*W4(r-1, a+4)
r2 = 2 + p
I4b = sp.Rational(1, 4)*(B(r2, a+2)*Bp(r2-2, a+4)*Dn(r2-1) + Bp(r2-1, a+2)*B(r2-2, a+4)*Dn(r2)) - W4(r2-2, a+4)*Dn(r2)*Dn(r2-1)
for name, e in (('I3', I3), ('I4a', I4a), ('I4b', I4b)):
    test(name, e, None, lc=True)
    test(name, e, None, lc=False)
