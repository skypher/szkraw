"""Edge coefficients e_n of the forms R, R2 (step (iii')) and K_a, Psi, Qhat (step (v)) of Theorem 8.16, mirrored on
the Lean definitions (lean/Szkraw/GenFormK.lean, GenFormKpp.lean): cfAD = C(a,n) - C(1,n), cfXp, cfXpp, cfJ, cfY,
cfYp, cfH, ePos = edge(cfYp,cfXpp) + edge(cfY,cfXp).
  R    = a edge(cfAD,cfXp) - 8 (H_n + H_{n+1})
  R2   = (a-2) edge(cfAD,cfXpp) - 4a (H_n + H_{n+1})
  Ka   = (a-1) ePos - 4a (H_n + H_{n+1})
  Psi  = a edge(cfAD,cfJ) - C(a-1,2) (Y_n + Y'_n)
  Qhat = (a-1) ePos + (2(n+1)^2 - 4a) H_{n+1} - 4 (a + C(a,2) - n - C(n,2)) H_n
Prints: e_n for n = 0..3 as polynomials in a (and their coefficients after a -> a + a0), e_{a+1}, and the generic
certificate (n = p+4 <= a = n+K, relative to c = C(a,n)): cleared numerator, its negative coefficients (must be none).
Also checks every e_n >= 0 exactly for a0 <= a <= 40. Usage: forms_iii_v.py"""
import sympy as sp
from math import comb

A0 = {'R': 3, 'R2': 6, 'Ka': 5, 'Psi': 3, 'Qhat': 3}

def seqs(a, Cf):
    C = Cf
    AD = lambda n: C(a, n) - C(1, n)
    Xp = lambda n: C(a - 1, n) - C(1, n)
    Xpp = lambda n: C(a - 1, n) - C(0, n)
    J = lambda n: C(a - 1, n) if n >= 2 else 0
    Y = lambda n: C(a, n) - C(0, n) - a * (C(1, n) - C(0, n))
    Yp = lambda n: C(a, n) + (a - 2) * C(1, n) - (a - 1) * C(2, n)
    H = lambda n: (n - 2) * C(a, n) if n >= 3 else 0
    def edge(x, y, n):
        v = x(1) * y(n) + x(2) * (y(n - 1) if n >= 1 else 0)
        if n >= 3: v += y(1) * x(n)
        if n >= 4: v += y(2) * x(n - 1)
        return v
    ePos = lambda n: edge(Yp, Xpp, n) + edge(Y, Xp, n)
    return {
        'R': lambda n: a * edge(AD, Xp, n) - 8 * (H(n) + H(n + 1)),
        'R2': lambda n: (a - 2) * edge(AD, Xpp, n) - 4 * a * (H(n) + H(n + 1)),
        'Ka': lambda n: (a - 1) * ePos(n) - 4 * a * (H(n) + H(n + 1)),
        'Psi': lambda n: a * edge(AD, J, n) - C(a - 1, 2) * (Y(n) + Yp(n)),
        'Qhat': lambda n: (a - 1) * ePos(n) + (2 * (n + 1) ** 2 - 4 * a) * H(n + 1)
                          - 4 * (a + C(a, 2) - n - C(n, 2)) * H(n),
    }

def Cint(n, k):
    return comb(n, k) if 0 <= k <= n and n >= 0 else 0

# exact check
for a in range(3, 41):
    for name, e in seqs(a, Cint).items():
        if a < A0[name]: continue
        bad = [n for n in range(a + 4) if e(n) < 0]
        assert not bad, (name, a, bad)
print('exact: all e_n >= 0 for a0 <= a <= 40')

a, t = sp.symbols('a t')
def Csym(n, k):  # symbolic in the top argument, numeric k
    if isinstance(k, int) and k < 0: return 0
    return sp.expand(sp.binomial(n, k).expand(func=True)) if isinstance(k, int) else sp.binomial(n, k)
S = seqs(a, Csym)
for name, e in S.items():
    print(f'== {name} (a0 = {A0[name]})')
    for n in range(4):
        v = sp.expand(e(n))
        shifted = sp.Poly(sp.expand(v.subs(a, t + A0[name])), t)
        print(f'  n={n}: {sp.factor(v)}   coeffs at a = t + a0: {shifted.all_coeffs()}')

# generic n = p + 4, a = n + K, relative to c = C(a,n)
p, K, c = sp.symbols('p K c', nonnegative=True)
n = p + 4; aa = n + K
rat = {('a', 0): 1, ('a', -1): n / (K + 1), ('a', 1): K / (n + 1), ('a1', 0): K / aa, ('a1', -1): n / aa}
def gen(name):
    x1 = {'AD': aa - 1}; x2 = {'AD': aa * (aa - 1) / 2}
    AD = lambda o: rat[('a', o)]
    Xp1, Xp2 = aa - 2, (aa - 1) * (aa - 2) / 2
    Xpp1, Xpp2 = aa - 1, (aa - 1) * (aa - 2) / 2
    J1, J2 = 0, (aa - 1) * (aa - 2) / 2
    Y1, Y2, Yp1, Yp2 = 0, aa * (aa - 1) / 2, 0, aa * (aa - 1) / 2 - (aa - 1)
    a1 = lambda o: rat[('a1', o)]
    edge = lambda X1, X2, xs, Y1_, Y2_, ys: X1 * ys(0) + X2 * ys(-1) + Y1_ * xs(0) + Y2_ * xs(-1)
    H0, H1 = (n - 2) * 1, (n - 1) * rat[('a', 1)]
    ePos = edge(Yp1, Yp2, AD, Xpp1, Xpp2, a1) + edge(Y1, Y2, AD, Xp1, Xp2, a1)
    return {
        'R': aa * edge(aa - 1, aa * (aa - 1) / 2, AD, Xp1, Xp2, a1) - 8 * (H0 + H1),
        'R2': (aa - 2) * edge(aa - 1, aa * (aa - 1) / 2, AD, Xpp1, Xpp2, a1) - 4 * aa * (H0 + H1),
        'Ka': (aa - 1) * ePos - 4 * aa * (H0 + H1),
        'Psi': aa * edge(aa - 1, aa * (aa - 1) / 2, AD, J1, J2, a1) - (aa - 1) * (aa - 2) / 2 * 2,
        'Qhat': (aa - 1) * ePos + (2 * (n + 1) ** 2 - 4 * aa) * H1 - 4 * (aa + aa * (aa - 1) / 2 - n - n * (n - 1) / 2) * H0,
    }[name]
for name in S:
    e = sp.together(gen(name)); num, den = sp.fraction(e)
    P = sp.Poly(sp.expand(num), p, K)
    neg = [(m, co) for m, co in zip(P.monoms(), P.coeffs()) if co < 0]
    print(f'== {name} generic: denominator {sp.factor(den)}; negative coefficients: {neg}')
    print(f'   numerator: {sp.expand(num)}')
    # sanity: matches the integer sequences
    for aval in range(4, 14):
        for nval in range(4, aval + 1):
            exact = seqs(aval, Cint)[name](nval) / comb(aval, nval)
            g = gen(name).subs({p: nval - 4, K: aval - nval})
            assert sp.nsimplify(g) == sp.Rational(exact).limit_denominator(10**12) or abs(float(g) - exact) < 1e-9, (name, aval, nval)
print('generic formulas agree with the exact sequences for 4 <= n <= a <= 13')
