import sympy as sp
rho, a, s2, s3, lam = sp.symbols('rho a s2 s3 lam', nonnegative=True)
r = 1 + rho
C2 = lambda n: n*(n - 1)/2; C3 = lambda n: n*(n - 1)*(n - 2)/6
D = lambda n: n + C2(n)*s2 + C3(n)*s3
B = lambda rr, aa: C2(aa)*(s2 + rr*s3) + C3(aa)*s3
LHS = (D(r + a + 1) - D(r))*B(r - 1, a + 3) + (D(r + a + 2) - D(r - 1))*B(r, a + 2)
RHS = D(r)*s3*C3(a + 3)
for fac in (1, 2, 4):
    P = sp.Poly(sp.expand(LHS - fac*RHS), rho, a, s2, s3)
    neg = [(m, c) for m, c in P.terms() if c < 0]
    print(f'factor {fac}: {len(P.terms())} terms, {len(neg)} negative: {neg[:6]}')
# ratio at a few points
f = sp.lambdify((rho, a, s2, s3), LHS/RHS)
import itertools
worst = min((f(x, y, p, q), (x, y, p, q)) for x in (0, 1, 3, 10, 100) for y in (0, 1, 3, 10, 100) for p in (0, 0.01, 1, 100) for q in (0.01, 1, 100))
print('min LHS/RHS on grid:', worst)
