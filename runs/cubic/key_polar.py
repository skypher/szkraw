"""Cubic key, polarized in rho = (r, t, tau, sigma) (basis e_0..e_3), B_0 kept exact, alpha = s R_l (R_l = u0/u1;
the alpha-coefficient X B0' + B0 X' - 4 c H* >= rho(l+1) K >= 0). Key = A0 B0(l+1,a-1) + B0(l,a) A0'' - c (4 H1 - 2 V^q_1 - W^tau_1)
is then a quadratic form sum kappa_bg rho_b rho_g in rho with coefficients bilinear in u.
Decomposition (as for the B-detour): Key = Key(r,0,tau,0) [Theorem 8.11, >= 0] + t(k_rt r + k_tt t + k_ttau tau)
+ sigma(k_rs r + k_ts t + k_taus tau + k_ss sigma); with r sigma <= t tau it suffices that
k_rt, k_tt, k_ts, k_taus, k_ss, k_ttau, k_ttau + k_rs >= 0. main: test on random LC u, u0 <= min(l u1, u1^2/u2),
including geometric small-q configurations. Usage: key_polar.py trials seed [none|lin|full]"""
import sys, math, random
from fractions import Fraction as F
C = math.comb
def e(b, x): return C(x, b) if x >= 0 else 0
VSIG = 'lin'   # sigma part of V kept in the V family: 'none', 'lin' = n (l/2)(l+n-1) f_{n-1}, 'full' = n C(l+n-1,2) f_{n-1},
# 'loc' = n (C(l,2) + l(n-1)) f_{n-1} together with the W family C(n,2)(tau + sigma l) f_{n-2}
def vshape(b, l, n):
    if b in (1, 2): return e(b - 1, l + n - 1)
    if b == 3: return {'none': 0, 'lin': F(l, 2) * (l + n - 1), 'full': e(2, l + n - 1), 'loc': e(2, l) + l * (n - 1)}[VSIG]
    return 0
def key_coeffs(u, l, a):
    U = lambda k: u[k] if 0 <= k < len(u) else 0
    y = lambda n: C(a, n) * U(n); D = U(0) + U(1); R = U(0) / U(1)
    X = sum(y(n) for n in range(1, a + 1)); Xp = sum(C(a - 2, j) * (U(j) + U(j + 1)) for j in range(1, a - 1))
    def phi(b, n, ll, sh):  # phi_n[e_b](ll) with f_k = u_k (+ u_{k+1} if sh)
        return sum(C(n, i) * e(b - i, ll + n - i) * (U(n - i) + (U(n - i + 1) if sh else 0)) for i in range(0, min(b, n) + 1))
    B0 = [sum(C(a, n) * phi(b, n, l, 0) for n in range(2, a + 1)) for b in range(4)]
    B0p = [sum(C(a - 1, n) * phi(b, n, l + 1, 1) for n in range(2, a)) for b in range(4)]
    c = [e(b, l + 1) * D for b in range(4)]
    s = [e(b - 1, l + a - 1) if b >= 1 else 0 for b in range(4)]
    al = [s[b] * R for b in range(4)]
    A0 = [al[b] * X - (e(b, l + a) - e(b, l)) * U(0) for b in range(4)]
    A0b = [(al[b] + s[b]) * Xp - (e(b, l + a - 1) - e(b, l + 1)) * D for b in range(4)]
    H1 = [sum((n - 2) * y(n) * (al[b] + e(b, l + a) - e(b, l + n)) for n in range(3, a + 1)) for b in range(4)]
    V1 = [sum((n - 2) * C(a, n) * n * vshape(b, l, n) * U(n - 1) for n in range(3, a + 1)) for b in range(4)]
    wsh = [0, 0, 1, (l if VSIG == 'loc' else 0)]
    W1 = [wsh[b] * sum((n - 2) * C(a, n) * C(n, 2) * U(n - 2) for n in range(3, a + 1)) for b in range(4)]
    Q = [4 * H1[b] - 2 * V1[b] - W1[b] for b in range(4)]
    k = {}
    for b in range(4):
        for g in range(b, 4):
            v = A0[b] * B0p[g] + B0[b] * A0b[g] - c[b] * Q[g]
            if g != b: v += A0[g] * B0p[b] + B0[g] * A0b[b] - c[g] * Q[b]
            k[(b, g)] = v
    return k
NM = {'rt': (0, 1), 'tt': (1, 1), 'ts': (1, 3), 'taus': (2, 3), 'ss': (3, 3), 'ttau': (1, 2), 'rs': (0, 3)}
if __name__ == '__main__':
    T, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
    if len(sys.argv) > 3: VSIG = sys.argv[3]
    worst = {}
    for it in range(T):
        a = rng.randint(3, 16); l = rng.choice([0, 1, 2, 3, 5, 10, 30, 100, 1000, 10 ** 5])
        if it % 2 == 0:
            q = F(rng.randint(1, 100), 10) ** rng.choice([-3, -2, -1, 1]); rat = [q] * a
        else:
            rat = sorted((F(rng.randint(1, 1000), rng.choice([1, 10, 100, 1000])) for _ in range(a)), reverse=True)
        u = [F(0), F(1)]
        for x in rat: u.append(u[-1] * x)
        u = u[:a + 1]; q = u[2]; zmax = min(F(l), 1 / q)
        u[0] = zmax if rng.random() < .6 else zmax * F(rng.randint(0, 10), 10)
        k = key_coeffs(u, l, a)
        sc = (u[0] + u[1]) * sum(C(a, n) * u[n] for n in range(2, a + 1)) * (1 + l) ** 4
        vals = {nm: k[NM[nm]] for nm in NM}; vals['ttau+rs'] = vals['ttau'] + vals['rs']
        for nm, v in vals.items():
            if nm not in worst or v / sc < worst[nm][0]: worst[nm] = (v / sc, l, a, float(q), float(u[0]))
    for nm in ('rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'rs', 'ttau+rs'):
        w = worst[nm]; print(f'{nm}: min normalized {float(w[0]):.4g} at l={w[1]} a={w[2]} q={w[3]:.3g} z={w[4]:.3g}')
