import sympy as sp
from cubic_symbolic import G
a_, r_, t_, T_ = sp.symbols('a r t T'); s2, s3, s4 = sp.symbols('s2 s3 s4', nonnegative=True)
al, rr = sp.symbols('alpha rr', nonnegative=True)
g = G(4, [sp.Integer(1), s2, s3, s4])
Dn = lambda n: n + n*(n-1)/2*s2 + n*(n-1)*(n-2)/6*s3 + n*(n-1)*(n-2)*(n-3)/24*s4
for key, name, shift in (((-2, 0), 'B', 2), ((-2, 1), "B'", 2), ((-1, 0), 'A (t-move)', 1)):
    e = sp.expand(g[key].subs({a_: shift + al, r_: rr}))
    if key == (-1, 0): e = sp.expand(e/t_)
    P = sp.Poly(e, al, rr, s2, s3, s4)
    print(f'{name} at a = {shift} + alpha: {len(P.terms())} terms, {sum(1 for m, c in P.terms() if c < 0)} negative')
print('(0,0) coefficient equals T - D_{r+a}:', sp.expand(g[(0, 0)] - (T_ - Dn(r_ + a_))) == 0)
print('(0,-1) coefficient equals -D_r:', sp.expand(g[(0, -1)] + Dn(r_)) == 0)
print('A equals D_{r+a} - D_r:', sp.expand(g[(-1, 0)]/t_ - (Dn(r_ + a_) - Dn(r_))) == 0)
