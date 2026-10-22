"""Independent exact checks of consult round 7 (reviews/consult-I-answer.md), class (Q):
LC Newton profile d, rho(x) = r + t x + tau C(x,2), b nondecreasing.
 (1) weighted scalar B-detour (n+1)(n+2) phi_2(l) phi_n(l+1) >= 8(n-1) c_{l+1} phi_{n+2}(l), n >= 2, l+n+2 <= N;
 (31) summed B-detour 4 c B_j <= B_0 B'_{j-1};
 (2) key: A0 B0' + B0 A0'' >= c (4 H1 - 2 V1 - W1), a >= 3;
 (10), (13), (14) identities; (15) certificate; mixed detours 10, 9/2, 3, 6;
 M >= 0 and (P) for N <= 9; the scalar counterexample of section 5."""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq
from probe import linearization, first_negative
from resum_test import Mmin
C = math.comb
fails = {}
def bad(k, info=None):
    fails[k] = fails.get(k, 0) + 1
    if fails[k] <= 3: print('FAIL', k, info, flush=True)

def member(rng, N):
    mode = rng.randrange(4)
    if mode == 0: sig = lc_seq(rng, N)
    elif mode == 1:
        q = F(rng.choice([1, 2, 3, 5, 10, 50]), rng.choice([1, 2, 10, 100])); sig = [q ** j for j in range(N)]
    elif mode == 2: sig = [F(1), F(rng.randint(0, 30), rng.choice([1, 10]))] + [F(0)] * (N - 2)
    else:
        q = F(rng.choice([1, 2, 5]), rng.choice([10, 100])); K = rng.randint(1, N)
        sig = [q ** j if j < K else F(0) for j in range(N)]
    D = [sum(C(n, j) * sig[j - 1] for j in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]
    r = F(rng.randint(1, 19), 20); R = d[N - 1] / (1 - d[N - 1])
    lam = F(rng.randint(0, 10), 10); fill = F(rng.randint(1, 10), 10) if rng.random() < .5 else F(1)
    budget = (1 - r) * fill
    t = lam * budget / (N + R); tau = (1 - lam) * budget / (F(N * (N - 1), 2) + (N - 1) * R)
    return d, r, t, tau

def check(d, r, t, tau, full):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
    if any(b[i + 1] < b[i] for i in range(N)): bad('b mono')
    dif = lambda x, n, l: sum((-1) ** (n - i) * C(n, i) * x[l + i] for i in range(n + 1))
    fF = lambda n, l: dif(d, n, l) if n >= 0 else F(0)
    phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rho(l + n)) * fF(n, l)
    v = lambda n, l: n * (t + tau * (l + n - 1)) * fF(n - 1, l)
    w = lambda n, l: C(n, 2) * tau * fF(n - 2, l)
    W = lambda s, p, q, l, a: sum(C(nn - p + q, q) * C(a, nn) * s(nn, l) for nn in range(p, a + 1))
    # (1)
    for l in range(N + 1):
        for n in range(2, N + 1):
            if l + n + 2 > N: break
            if (n + 1) * (n + 2) * phi(2, l) * phi(n, l + 1) < 8 * (n - 1) * c[l + 1] * phi(n + 2, l): bad('(1)', (N, l, n))
    for l in range(N):
        cc = c[l + 1]
        for a in range(0, N + 1 - l):
            B0 = W(phi, 2, 0, l, a)
            for j in range(1, N + 1):
                if a < 2 * j + 2: break
                if 4 * cc * W(phi, 2 * j + 2, j, l, a) > B0 * W(phi, 2 * j, j - 1, l + 1, a - 2): bad('(31)', (N, l, a, j))
            for j in range(2, N + 1):
                if a < 2 * j + 1: break
                for name, mu, s in [('H', 10, h), ('V', F(9, 2), v), ('W', 3, w)]:
                    if mu * cc * W(s, 2 * j + 1, j, l, a) > B0 * W(s, 2 * j - 1, j - 1, l + 1, a - 2): bad('det' + name, (N, l, a, j))
            for j in range(1, N + 1):
                if a < 2 * j + 2: break
                if 6 * cc * W(fF, 2 * j + 2, j + 1, l, a) > B0 * W(fF, 2 * j, j, l + 1, a - 2): bad('detC', (N, l, a, j))
            if a >= 3:
                A0 = b[l + a] - b[l]; A0pp = b[l + a - 1] - b[l + 1]
                H1 = W(h, 3, 1, l, a); V1 = W(v, 3, 1, l, a); W1 = W(w, 3, 1, l, a)
                lhs = A0 * W(phi, 2, 0, l + 1, a - 1) + B0 * A0pp
                if lhs < cc * (4 * H1 - 2 * V1 - W1): bad('(2)', (N, l, a))
                # identities (10), (13), (14) in normalized-free form
                u = [fF(n, l) for n in range(a + 1)]
                al = 1 - rho(l + a); s_ = t + tau * (l + a - 1); z = u[0]; D = d[l + 1]
                y = [C(a, n) * u[n] for n in range(a + 1)]
                X = sum(y[1:]); Y = sum(y[2:])
                Xp = sum(C(a - 2, jj) * (fF(jj, l + 1)) for jj in range(1, a - 1))
                Yp = sum(C(a - 1, jj) * fF(jj, l + 1) for jj in range(2, a))
                if A0 != al * X - s_ * a * z + tau * C(a, 2) * z: bad('(10a)', (N, l, a))
                if A0pp != (al + s_) * Xp - s_ * (a - 2) * D + tau * C(a - 1, 2) * D: bad('(10b)', (N, l, a))
                Hs = sum((n - 2) * y[n] for n in range(3, a + 1)); Ts = sum((n - 3) * (a - n) * y[n] for n in range(2, a + 1))
                Z = sum(C(a - n, 2) * y[n] for n in range(2, a + 1))
                if 4 * H1 - 2 * V1 != 4 * al * Hs + 2 * s_ * Ts + 4 * tau * Z: bad('(13)', (N, l, a))
                if W1 != tau * sum(n * C(a - n, 2) * y[n] for n in range(1, a + 1)): bad('(14)', (N, l, a))
                if al < s_ * R_(d, l + a - 1): bad('(9)', (N, l, a))
    if full:
        if Mmin(a_, b, c)[0] < 0: bad('M', N)
        if first_negative(linearization(a_, b, c)): bad('(P)', N)

def R_(d, i): return d[i] / (d[i + 1] - d[i])

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); n = 0
    for N in [int(x) for x in sys.argv[2].split(',')]:
        for _ in range(int(sys.argv[3])):
            d, r, t, tau = member(rng, N); check(d, r, t, tau, N <= 9); n += 1
        print(N, 'arrays', n, fails, flush=True)
    # section 5 counterexample
    N = 20; d = [F(2 ** i - 1, 2 ** 20 - 1) for i in range(21)]; r = F(1, 2); t = F(0); tau = F(1, 1000)
    rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
    c = [rho(i) * d[i] for i in range(N + 1)]
    dif = lambda x, nn, l: sum((-1) ** (nn - i) * C(nn, i) * x[l + i] for i in range(nn + 1))
    val = dif(c, 2, 16) * dif(c, 2, 17) - c[17] * dif(c, 4, 16)
    R = d[19] / (1 - d[19])
    print('counterexample value', val, 'in Q:', tau * (C(20, 2) + 19 * R) < 1 - r)
    print('FINAL', fails)
