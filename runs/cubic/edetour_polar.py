"""Merged family E_n = C(n,2)(tau + sigma l) f_{n-2} + sigma E3_n, E3_n = C(n,3)(3 f_{n-1} + 3 f_{n-2} + f_{n-3})
(V keeps n(t + tau(l+n-1) + sigma(C(l,2) + l(n-1))) f_{n-1}). Pointwise detour, n >= 3:
  P(l,n) = (n+1)(n+2) phi_2(l) E_n(l+1) - MU (n-1) c_{l+1} E_{n+2}(l) >= 0,
polarized in rho = (r,t,tau,sigma) (E is linear in (tau, sigma), phi_2 and c in rho). With r sigma <= t tau it
suffices: all coefficients >= 0 except k_rs, and k_ttau + min(k_rs, 0) >= 0. Test on random LC u with
u0 <= min(l u1, u1^2/u2) (geometric small/large q included). PHI3: phi_2 replaced by phi_2 + (n/3) phi_3.
Usage: edetour_polar.py trials seed MU"""
import sys, math, random
PHI3 = True
from fractions import Fraction as F
C = math.comb
def e(b, x): return C(x, b) if x >= 0 else 0
def coeffs(u, l, n, MU):
    U = lambda k: u[k] if 0 <= k < len(u) else 0
    f0 = lambda k: U(k); f1 = lambda k: U(k) + U(k + 1)
    phi2 = [sum(C(2, i) * e(b - i, l + 2 - i) * U(2 - i) for i in range(0, min(b, 2) + 1)) for b in range(4)]
    if PHI3:  # B_0(l,a) >= C(a,2) phi_2 + C(a,3) phi_3 and C(a,3) C(a-2,n) = ((a-2)/3) C(a,n+2) C(n+2,2), a >= n+2
        phi3 = [sum(C(3, i) * e(b - i, l + 3 - i) * U(3 - i) for i in range(0, min(b, 3) + 1)) for b in range(4)]
        phi2 = [phi2[b] + F(n, 3) * phi3[b] for b in range(4)]
    c = [e(b, l + 1) * (U(0) + U(1)) for b in range(4)]
    def E(nn, ll, f):  # (tau-part, sigma-part)
        if nn < 2: return (0, 0)
        tp = C(nn, 2) * f(nn - 2)
        sp_ = ll * C(nn, 2) * f(nn - 2) + (C(nn, 3) * (3 * f(nn - 1) + 3 * f(nn - 2) + (f(nn - 3) if nn >= 3 else 0)))
        return (tp, sp_)
    Es, Et = E(n, l + 1, f1), E(n + 2, l, f0)
    k = {}
    for b in range(4):
        for gi, g in ((0, 2), (1, 3)):
            v = (n + 1) * (n + 2) * phi2[b] * Es[gi] - MU * (n - 1) * c[b] * Et[gi]
            key = (min(b, g), max(b, g)); k[key] = k.get(key, 0) + v
    return k
NAMES = {(0, 2): 'rtau', (0, 3): 'rs', (1, 2): 'ttau', (1, 3): 'ts', (2, 2): 'tautau', (2, 3): 'taus', (3, 3): 'ss'}
if __name__ == '__main__':
    T, rng, MU = int(sys.argv[1]), random.Random(int(sys.argv[2])), F(sys.argv[3])
    worst = {}
    for it in range(T):
        n = rng.randint(3, 12); l = rng.choice([0, 1, 2, 3, 5, 10, 30, 100, 1000])
        if it % 2 == 0:
            q = F(rng.randint(1, 100), 10) ** rng.choice([-3, -2, -1, 1, 2]); rat = [q] * (n + 4)
        else:
            rat = sorted((F(rng.randint(1, 1000), rng.choice([1, 10, 100, 1000])) for _ in range(n + 4)), reverse=True)
        u = [F(0), F(1)]
        for x in rat: u.append(u[-1] * x)
        q = u[2]; zmax = min(F(l), 1 / q)
        u[0] = zmax * F(rng.choice([0, 3, 7, 10, 10]), 10)
        k = coeffs(u, l, n, MU)
        sc = (u[0] + u[1]) * sum(u[n - 3:n + 3]) * (1 + l) ** 3 * (n + 1) ** 4
        vals = {NAMES[key]: v for key, v in k.items()}; vals['ttau+rs'] = vals['ttau'] + min(vals['rs'], 0)
        for nm, v in vals.items():
            if nm not in worst or v / sc < worst[nm][0]: worst[nm] = (v / sc, l, n, float(q), float(u[0]))
    for nm in ('rtau', 'rs', 'ttau', 'ttau+rs', 'ts', 'tautau', 'taus', 'ss'):
        w = worst[nm]; print(f'MU={MU} {nm}: min normalized {float(w[0]):.3g} at l={w[1]} n={w[2]} q={w[3]:.3g} z={w[4]:.3g}')
