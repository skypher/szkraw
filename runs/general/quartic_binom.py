"""Express the quartic positive weights in the binomial basis C(a,i) C(r,j) (nonnegative coefficients => nonnegative at
all integers a, r >= 0)."""
import sympy as sp
from cubic_symbolic import G
a_, r_, t_ = sp.symbols('a r t'); s2, s3, s4 = sp.symbols('s2 s3 s4')
g = G(4, [sp.Integer(1), s2, s3, s4])
def binom_basis(e, maxi=6, maxj=6):
    # Newton forward differences in a and r at 0: coefficient of C(a,i)C(r,j) = Delta_a^i Delta_r^j e (0,0)
    out = {}
    for i in range(maxi + 1):
        for j in range(maxj + 1):
            v = sum((-1)**(i - p)*sp.binomial(i, p)*(-1)**(j - q)*sp.binomial(j, q)*e.subs({a_: p, r_: q}) for p in range(i + 1) for q in range(j + 1))
            v = sp.expand(v)
            if v != 0: out[(i, j)] = v
    return out
for key, name, div in (((-2, 0), 'B', 1), ((-2, 1), "B'", 1), ((-1, 0), 'A', t_)):
    bb = binom_basis(sp.expand(g[key]/div))
    neg = {k: v for k, v in bb.items() if any(c < 0 for c in sp.Poly(v, s2, s3, s4).coeffs())}
    print(f'{name}: binomial-basis coefficients {bb}; negative: {neg}')
