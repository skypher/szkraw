"""Cubic key (u = 1 route): A0(l,a) B0(l+1,a-1) + B0(l,a) A0(l+1,a-2) >= c (4 H1 - 2 V^q_1 - W^tau_1).
With B0 >= p Y, p Y' (p = rho(l+1)), c = p D, alpha = 1 - rho(l+a) >= s u0/u1 (b nondecreasing; coefficient K >= 0),
s = t + tau(l+a-1) + sig C(l+a-1,2), tau' = tau + sig(l+a-2), the reduced key Phi = A0 Y' + Y A0'' - D(4H1 - 2V1 - W1)
at alpha = s u0/u1 is linear: Phi = t Phi_t + tau Phi_tau + sig Phi_sig. This module gives the closed forms;
main: (1) checks them against direct definitions on random cubic arrays; (2) tests the signs of Phi_t, Phi_tau,
Phi_sig on random log-concave u with u0 <= min(l u1, u1^2/u2). Usage: key_parts.py trials seed"""
import sys, math, random
from fractions import Fraction as F
C = math.comb
def parts(u, l, a, t, tau, sig, alpha=None):
    s = t + tau * (l + a - 1) + sig * C(l + a - 1, 2); tp = tau + sig * (l + a - 2); sq = t + tau * (l + a - 1)
    if alpha is None: alpha = s * u[0] / u[1]
    U = lambda k: u[k] if 0 <= k < len(u) else 0
    y = lambda n: C(a, n) * U(n)
    D = U(0) + U(1)
    X = sum(y(n) for n in range(1, a + 1)); Y = sum(y(n) for n in range(2, a + 1))
    Xp = sum(C(a - 2, j) * (U(j) + U(j + 1)) for j in range(1, a - 1)); Yp = sum(C(a - 1, j) * (U(j) + U(j + 1)) for j in range(2, a))
    A0 = alpha * X - a * s * U(0) + C(a, 2) * tp * U(0) - C(a, 3) * sig * U(0)
    A0b = (alpha + s) * Xp - (a - 2) * s * D + C(a - 1, 2) * tp * D - C(a - 1, 3) * sig * D
    H1 = sum((n - 2) * y(n) * (alpha + (a - n) * s - C(a - n, 2) * tp + C(a - n, 3) * sig) for n in range(3, a + 1))
    V1 = sum((k - 1) * (a - k) * (sq - tau * (a - k - 1)) * y(k) for k in range(2, a + 1))
    W1 = tau * sum(k * C(a - k, 2) * y(k) for k in range(1, a + 1))
    return dict(A0=A0, A0b=A0b, H1=H1, V1=V1, W1=W1, Y=Y, Yp=Yp, D=D, Phi=A0 * Yp + Y * A0b - D * (4 * H1 - 2 * V1 - W1))
if __name__ == '__main__':
    T, rng = int(sys.argv[1]), random.Random(int(sys.argv[2]))
    sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'varratio'))
    from hform import lc_seq
    # (1) closed forms vs direct definitions
    mism = 0
    for _ in range(40):
        N = rng.randint(5, 10); sg = lc_seq(rng, N)
        Dd = [sum(C(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]; d = [z / Dd[N] for z in Dd]
        r, t, tau, sig = [F(rng.randint(0, 9), rng.randint(1, 50)) for _ in range(4)]
        rho = lambda x: r + t * x + tau * C(x, 2) + sig * C(x, 3)
        c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
        dif = lambda xs, n, l: sum((-1) ** (n - i) * C(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
        f = lambda n, l: dif(d, n, l) if n >= 0 else F(0)
        h = lambda n, l: (1 - rho(l + n)) * f(n, l)
        vq = lambda n, l: n * (t + tau * (l + n - 1)) * f(n - 1, l)
        wt = lambda n, l: C(n, 2) * tau * f(n - 2, l)
        Wf = lambda s_, p, q, l, a: sum(C(n - p + q, q) * C(a, n) * s_(n, l) for n in range(p, a + 1))
        for l in range(N):
            for a in range(3, N + 1 - l):
                u = [f(k, l) for k in range(a + 1)]
                P = parts(u, l, a, t, tau, sig, alpha=1 - rho(l + a))
                ref = dict(A0=b[l + a] - b[l], A0b=b[l + a - 1] - b[l + 1], H1=Wf(h, 3, 1, l, a), V1=Wf(vq, 3, 1, l, a), W1=Wf(wt, 3, 1, l, a))
                mism += sum(P[k] != v for k, v in ref.items())
    print('closed forms vs definitions: mismatches', mism)
    # (2) signs of Phi_t, Phi_tau, Phi_sig on random LC u, u0 <= min(l u1, u1^2/u2)
    worst = {}
    for _ in range(T):
        a = rng.randint(3, 14); l = rng.choice([0, 1, 2, 3, 5, 8, 13, 30, 100])
        qs = sorted((F(rng.randint(1, 400), rng.choice([1, 10, 100])) for _ in range(a + 1)), reverse=True)
        u = [F(0), F(1)]
        for x in qs: u.append(u[-1] * x / (1 if rng.random() < .8 else 10))
        u = [F(0), F(1)] + [F(1)] * 0 + u[2:]
        # enforce LC: rebuild from sorted ratios
        rat = sorted([u[k + 1] / u[k] for k in range(1, len(u) - 1)], reverse=True)
        u = [F(0), F(1)]
        for x in rat: u.append(u[-1] * x)
        q = u[2]; zmax = min(F(l), 1 / q) if q > 0 else F(l)
        u[0] = zmax * F(rng.choice([0, 1, 1, 1, rng.randint(0, 10)]), 10) if rng.random() < .5 else zmax
        for name, prm in (('t', (1, 0, 0)), ('tau', (0, 1, 0)), ('sig', (0, 0, 1))):
            v = parts(u, l, a, *map(F, prm))['Phi']
            sc = parts(u, l, a, *map(F, prm))['D'] * sum(C(a, n) * u[n] for n in range(2, a + 1)) * (1 + C(l + a, 2))
            key = name
            if key not in worst or v / sc < worst[key][0]: worst[key] = (v / sc, l, a)
    for k, v in worst.items(): print(f'Phi_{k}: worst normalized {float(v[0]):.4g} at (l, a) = {v[1:]}')
