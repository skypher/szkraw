"""Attempt positivity certificates for the reduced conditions (n >= 6) of each coefficient form kappa_X.
Regimes for z = u_0 (conditions are affine in z): z = 0; z = l with q = 1/(l + w) (w >= 0); z = 1/q = h with
l = h + w (h > 0, w >= 0). Condition (iii) with c = q s, s in [0,1], Bernstein form in s.
n = 6 + m. A polynomial is certified if all coefficients (in the nonnegative variables) are >= 0.
Reports per (kappa, condition, regime) whether certified and the number of negative coefficients."""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_sym import kap, l, n
z, q, c, s, m, w, h = sp.symbols('z q c s m w h', nonnegative=True)
TG = sys.argv[1:] or ['rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'ttau+rs']
def bern(P, var, deg):
    # Bernstein coefficients of polynomial P(var) on [0,1] of degree deg
    co = [sp.expand(P).coeff(var, k) for k in range(deg + 1)]
    return [sp.expand(sum(sp.binomial(i, k) / sp.binomial(deg, k) * co[k] for k in range(i + 1))) for i in range(deg + 1)]
def negs(expr, vars_):
    expr = sp.expand(expr)
    if expr == 0: return 0, 0
    if not expr.free_symbols: return (1 if expr < 0 else 0), 1
    P = sp.Poly(expr, *vars_)
    return sum(1 for cf in P.coeffs() if cf < 0), len(P.coeffs())
def main():
  for name in TG:
    g = kap(name)
    G = {j: sp.sympify(sum(v * {0: z, 1: 1, 2: q}[a] for (a, jj), v in g.items() if jj == j)) for j in range(-3, 3)}
    A = G[-1] + G[-2] / q + G[-3] / q ** 2
    conds = {'i': A * q ** 2, 'ii': (A + q * G[0]) * q ** 2, 'iii': None}
    iii = sp.expand((A + c * G[0] + c ** 2 * G[1] + c ** 3 * G[2]).subs(c, q * s) * q ** 2)
    zc = {k: sp.expand(v).coeff(z, 1) for k, v in conds.items() if v is not None}
    out = []
    for cname in ('i', 'ii', 'iii'):
        base = iii if cname == 'iii' else sp.expand(conds[cname])
        for reg in ('z0', 'zl', 'zh'):
            if reg == 'z0': e = base.subs(z, 0)
            elif reg == 'zl': e = base.subs(z, l).subs(q, 1 / (l + w))
            else: e = base.subs(z, h).subs(q, 1 / h).subs(l, h + w)
            e = sp.together(sp.expand(e.subs(n, m + 6)))
            num, den = sp.fraction(e)
            num = sp.expand(num)
            vars_ = sorted(num.free_symbols, key=str)
            if cname == 'iii' and s in num.free_symbols:
                deg = sp.degree(num, s)
                bs = bern(num, s, deg)
                tot = [negs(b, [v for v in vars_ if v != s]) for b in bs]
                nn = sum(t[0] for t in tot); nt = sum(t[1] for t in tot)
            else:
                nn, nt = negs(num, vars_)
            out.append(f'{cname}/{reg}:{"OK" if nn == 0 else f"{nn}/{nt}neg"}')
    print(name, ' '.join(out), flush=True)

if __name__ == '__main__':
    main()
