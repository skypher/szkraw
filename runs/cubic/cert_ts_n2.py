"""kappa_ts at n = 2 for l >= 1 (the corner l = 0 is genuinely negative and is repaired separately).
Endpoint a = q of the exact reduction (cert_lown.py): F = P0 + q (H_3 q + H_4 q^2). Regimes with l = 1 + L:
z = 0; z = l, q = 1/(l + w); z = h = 1/q <= l with h = 1 + H, l = h + w; and h = 1/(1 + k) < 1 <= l."""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kappa_sym import l
from small_n_forms import forms, u as U
from cert_try import negs
z, q, w, h, L, H, k = sp.symbols('z q w h L H k', nonnegative=True)
e = sp.expand(forms(2)['ts'].subs({U[0]: z, U[1]: 1, U[2]: q}))
H3, H4 = e.coeff(U[3], 1), e.coeff(U[4], 1)
P0 = sp.expand(e.subs({U[3]: 0, U[4]: 0}))
F = sp.expand(P0 + q * (H3 * q + H4 * q ** 2))
cases = {'z0': F.subs(z, 0).subs(l, 1 + L),
         'zl': F.subs(z, l).subs(q, 1 / (l + w)).subs(l, 1 + L),
         'zh,h>=1': F.subs(z, h).subs(q, 1 / h).subs(l, h + w).subs(h, 1 + H),
         'zh,h<1': F.subs(z, h).subs(q, 1 / h).subs(h, 1 / (1 + k)).subs(l, 1 + L)}
for name, ex in cases.items():
    num, den = sp.fraction(sp.together(sp.expand(ex)))
    num = sp.expand(num)
    print(name, 'negative coefficients / total:', negs(num, sorted(num.free_symbols, key=str)), ' den:', sp.factor(den))
print('l = 0 value at z = 0:', sp.factor(F.subs({l: 0, z: 0})))
