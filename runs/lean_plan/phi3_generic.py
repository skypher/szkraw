"""Generic-index certificates for the Phi3 edge forms eA, eB (runs/lean_plan/phi3_edge.py) of the cubic key:
n = p + 4 <= a = n + K, everything relative to c = C(a,n). Checks the cleared numerators have nonnegative coefficients
in (p, K), and cross-checks against the exact integer coefficients. Usage: phi3_generic.py"""
import sympy as sp
from math import comb as Cm
import importlib.util, os, sys
p, K = sp.symbols('p K', nonnegative=True)
n = p + 4; a = n + K
def C(x, k): return sp.expand(sp.expand_func(sp.binomial(x, k)))
s = C(a - 1, 2)
# ratios to c = C(a, n)
cA = {-1: n / (K + 1), 0: sp.Integer(1), 1: K / (n + 1), 2: K * (K - 1) / ((n + 1) * (n + 2)),
      3: K * (K - 1) * (K - 2) / ((n + 1) * (n + 2) * (n + 3))}
cA1 = {-1: n / a, 0: K / a}       # C(a-1, n+o) / C(a, n)
def X(o): return cA[o]             # cfX, n+o >= 1
def Y(o): return cA[o]             # cfY, n+o >= 2
def Yp(o): return cA[o]            # cfYp, n+o >= 3
def Xp(o): return cA1[o]           # cfXp, n+o >= 2
def H(o): return (n + o - 2) * cA[o]
def T3(o): return (n + o - 2) * cA[o] * (C(a, 3) - C(n + o, 3))
def W3(o): return (n + o - 2) * cA[o] * C(n + o, 3)
E3 = 3 * W3(1) + 3 * W3(2) + W3(3)
# first coefficients (x1, x2)
X1, X2 = a, a * (a - 1) / 2
Y1, Y2 = 0, a * (a - 1) / 2
Yp1, Yp2 = 0, a * (a - 1) / 2 - (a - 1)
Xp1, Xp2 = a - 2, (a - 1) * (a - 2) / 2
def edge(x1, x2, xs, y1, y2, ys): return x1 * ys(0) + x2 * ys(-1) + y1 * xs(0) + y2 * xs(-1)
eYX = edge(Y1, Y2, Y, Xp1, Xp2, Xp)
eXY = edge(X1, X2, X, Yp1, Yp2, Yp)
eA = s * eYX - C(a - 1, 3) * Y(0) - 4 * T3(0) + E3
eB = s * (eXY + eYX) - 4 * s * H(0) - 4 * s * H(1) - C(a, 3) * Yp(0) - C(a - 1, 3) * Y(0) - 4 * T3(0) + E3
for name, e in (('eA', eA), ('eB', eB)):
    num, den = sp.fraction(sp.together(sp.expand(e)))
    P = sp.Poly(sp.expand(num), p, K)
    neg = [(m, c) for m, c in zip(P.monoms(), P.coeffs()) if c < 0]
    print(name, 'den', sp.factor(den), 'terms', len(P.coeffs()), 'negative', neg[:5])
# cross-check with the exact integer sequences of phi3_edge.py
sys.argv = sys.argv[:1]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from phi3_edge import run
for av in range(4, 16):
    eAx, eBx = run(av)
    for nv in range(4, av + 1):
        sub = {p: nv - 4, K: av - nv}
        for gen, ex in ((eA, eAx), (eB, eBx)):
            assert sp.simplify(gen.subs(sub) - sp.Rational(ex[nv], Cm(av, nv))) == 0, (av, nv)
print('generic formulas agree with the exact coefficients for 4 <= n <= a <= 15')
