"""Corner (l, n) = (0, 2) of the cubic weighted B-detour, summed form.
In B_0(0,a) B_0(1,a-2) >= 4 c_1 B_1(0,a), the m = 4 term needs 6 C(a,4) phi_2(0) phi_2(1) >= 4 C(a,4) c_1 phi_4(0),
which fails pointwise. B_0(0,a) >= C(a,2) phi_2(0) + C(a,3) phi_3(0) and C(a,3) C(a-2,2) = 2(a-2) C(a,4) >= 4 C(a,4)
(a >= 4) give the extra 4 C(a,4) phi_3(0) phi_2(1); the other terms (n >= 3) use only C(a,2) phi_2(0).
So it suffices: Dc = (12 phi_2(0) + 8 phi_3(0)) phi_2(1) - 8 c_1 phi_4(0) >= 0 (u_0 = d_0 = 0).
Polarized, Dc = D(0,2) + 8 phi_3(0) phi_2(1), the added coefficients are all >= 0; only kappa_ts of D(0,2) can be < 0.
Certify kappa_ts + 8 [phi_3(0) phi_2(1)]_ts >= 0 for log-concave u with u_0 = 0, u_1 = 1, u_2 = q, u_3 = q a (a <= q),
u_4 <= q a^2. Asserts; prints CERTIFIED."""
import sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from small_n_forms import forms, u as U, _g, MON
from cert_try import bern, negs
q, a, s = sp.symbols('q a s', nonnegative=True)
r, t, tau, sig = _g['r'], _g['t'], _g['tau'], _g['sig']
RHO = _g['RHO']; Drho = _g['Drho']
# phi_m(l) = sum_i C(m,i) Delta^i rho(l+m-i) f_{m-i}(l), f_k(1) = u_k + u_{k+1}
f0 = {k: U[k] for k in range(8)}
f1 = {k: U[k] + U[k + 1] for k in range(7)}
def phi(m, lv, f):
    return sum(sp.binomial(m, i) * Drho(i, lv + m - i) * f[m - i] for i in range(0, min(m, 3) + 1))
extra = sp.expand(8 * phi(3, 0, f0) * phi(2, 1, f1))
P = sp.Poly(extra, r, t, tau, sig)
assert all(cf.subs({x: 1 for x in U}) >= 0 for cf in P.coeffs()) and all(sp.Poly(cf, *U).coeffs() and min(sp.Poly(cf, *U).coeffs()) >= 0 for cf in P.coeffs())
k_ts = sp.expand(forms(2)['ts'].subs(sp.Symbol('l', nonnegative=True), 0) + P.coeff_monomial(MON['ts']))
e = sp.expand(k_ts.subs({U[0]: 0, U[1]: 1, U[2]: q}))
assert sp.Poly(e, *U[3:8]).degree(U[4]) <= 1 and all(sp.Poly(e, *U[3:8]).degree(U[b]) == 0 for b in (5, 6, 7))
c4 = e.coeff(U[4], 1)
print('coefficient of u_4:', sp.factor(c4))
assert negs(sp.expand(-c4), [q, U[3]])[0] == 0  # <= 0, so u_4 = q a^2 is the worst case
F = sp.expand(e.subs(U[4], q * a ** 2).subs(U[3], q * a).subs(a, q * s))
for b in bern(F, s, sp.degree(F, s)):
    assert negs(b, [q])[0] == 0, b
print('corner kappa_ts:', sp.factor(F))
print('CERTIFIED: corner repair (12 phi_2(0) + 8 phi_3(0)) phi_2(1) >= 8 c_1 phi_4(0) under r sigma <= t tau')
