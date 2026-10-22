"""Symbolic checks of the polynomial certificates (24)-(30) of consult round 7."""
import sympy as sp
n, h, p, tau, s, sig, l, w, t = sp.symbols('n h p tau s sigma ell w t')
K = (n + 1) * (n + 2); L = 8 * (n - 1)
A = p + (2 * h - 1) * s + h ** 2 * tau
B = p + n * h * (s + tau) + n * (n - 1) / 2 * h ** 2 * tau
Cc = p + ((n + 2) * h - 1) * s + (n + 2) * (n + 1) / 2 * h ** 2 * tau
E = sp.expand(K * A * B - L * p * Cc)
an = n ** 2 - 5 * n + 10
Un = n ** 4 - 4 * n ** 3 - 21 * n ** 2 + 12 * n + 60
Cn = (h ** 2 * Un + h * (10 * n ** 2 + 14 * n - 60) + 2 * an) / 2
Dn = h ** 2 * n * (n + 1) ** 2 * (n + 2) * (3 * h ** 2 - 3 * h + 1) / 2
E0 = sp.expand(E.subs(s, (h - 1) * tau))
print('(25) identity:', sp.simplify(E0 - (an * p ** 2 + Cn * p * tau + Dn * tau ** 2)) == 0)
# monotone in s for s >= (h-1) tau: E(s = (h-1)tau + sig) - E0 has coefficients >= 0 in sig for n >= 2, h >= 1
Es = sp.expand(E.subs(s, (h - 1) * tau + sig) - E0)
poly = sp.Poly(Es, sig, p, tau)
ok = True
for mon, coef in zip(poly.monoms(), poly.coeffs()):
    for nn in range(2, 30):
        for hh in [1, sp.Rational(3, 2), 2, 3, 7, 20]:
            if coef.subs({n: nn, h: hh}) < 0: ok = False; print('neg coef', mon, nn, hh)
print('s-monotonicity coefficients nonneg (n=2..29, sampled h):', ok)
k = sp.symbols('k')
print('U_n at n=k+7:', sp.expand(Un.subs(n, k + 7)))
for nn in range(2, 7):
    v = sp.symbols('v')
    expr = sp.Poly(sp.expand((4 * an * Dn - Cn ** 2).subs({n: nn, h: v + 1})), v)
    print(nn, list(reversed(expr.all_coeffs())))
# C_n, D_n nonneg for n >= 7 (h >= 1): C_n terms
print('10n^2+14n-60 >= 0 at n=2:', 10*4+28-60)
