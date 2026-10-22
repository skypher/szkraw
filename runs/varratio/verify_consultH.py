"""Independent exact checks of consult round 6 (reviews/consult-H-answer.md).
(a) b nondecreasing <=> last increment >= 0 (quadratic convex ratios, LC Newton profiles); R_i = d_i/f_1(i) nondecreasing.
(b) affine key inequality steps: alpha >= t u0/u1 at every source; (6) at all sources for t at the new maximum;
    identity (9); F(0) >= 0 (13); F(1/q) >= 0 (14); bounds (10), (11), (15) on random and geometric LC sequences.
(c) mixed detour constants mu_H = 10, mu_V = 9/2, mu_W = 3, mu_C = 6 on random members of (Q).
(d) strict extension example N = 4; quadratic-profile subclass: (P) and M >= 0."""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq
from probe import linearization, first_negative
from resum_test import Mmin
C = math.comb

def lc_profile(rng, N):
    sig = lc_seq(rng, N)
    D = [sum(C(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    return [x / D[N] for x in D]
dif = lambda x, n, l: sum((-1) ** (n - i) * C(n, i) * x[l + i] for i in range(n + 1))
fails = {}
def bad(k, info=None):
    fails[k] = fails.get(k, 0) + 1
    if fails[k] <= 3: print('FAIL', k, info, flush=True)

def seq_checks(u, a):
    # u normalized: u[1] = 1
    y = [C(a, n) * u[n] for n in range(a + 1)]
    q = u[2]; z = u[0]
    Y = sum(y[2:]); J = sum(C(a - 1, n) * u[n] for n in range(2, a))
    Yp = sum(C(a - 1, j) * (u[j] + u[j + 1]) for j in range(2, a))
    Hs = sum((n - 2) * y[n] for n in range(3, a + 1)); T = sum((n - 3) * (a - n) * y[n] for n in range(2, a + 1))
    Fz = lambda zz: zz * Y * Yp + (zz + 1) * Y * J - (zz + 1) * (4 * zz * Hs + 2 * T)
    L = lambda n: F(3, 2) if n == 3 else F(n * (n + 2), 6)
    E = lambda n: F(2 * (n * n - 5), n + 1)
    if Yp != Y - (a - 1) * q: bad('Yp')
    if YJ := None: pass
    if Y * J < sum(L(n) * (a - n) * y[n] for n in range(3, a)): bad('(10)', a)
    if q > 0 and Y * Yp / (q + 1) < sum(F(n * (a - 1), 2) * y[n] for n in range(3, a + 1)): bad('(11)', a)
    if Fz(0) < 0: bad('(13)', a)
    if q > 0:
        if 4 * Hs / q + 2 * T > sum(E(n) * (a - n) * y[n] for n in range(2, a)): bad('(15)', a)
        if Fz(1 / q) < 0: bad('(14)', a)
        for zz in [z, F(0), 1 / q, 1 / (2 * q)]:
            if Fz(zz) != (1 - q * zz) * Fz(0) + q * zz * Fz(1 / q) + 4 * Hs * zz * (1 / q - zz): bad('(9)')
        if 0 <= z <= 1 / q and Fz(z) < 0: bad('F(z)', a)

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); n_arr = 0; n_src = 0; n_seq = 0
    # (b) sequences: random LC and geometric
    for a in range(3, 15):
        for _ in range(400):
            qs = sorted((F(rng.randint(1, 1000), rng.choice([10, 1000, 10 ** 5])) for _ in range(a + 2)), reverse=True)
            u = [F(1)]
            for k in range(a + 1): u.append(u[-1] * qs[k])
            u = [x / u[1] for x in u]; seq_checks(u, a); n_seq += 1
        for qq in [F(1, 10 ** k) for k in range(6)] + [F(1, 2), F(3)]:
            for z in [F(0), 1 / qq, 1 / (2 * qq)]:
                u = [z, F(1)] + [qq ** k for k in range(1, a + 1)]; seq_checks(u, a); n_seq += 1
    print('sequence checks', n_seq, fails, flush=True)
    # (a), (b) arrays with tau = 0 at the new maximal t; (c) quadratic ratios
    for N in range(3, 12):
        for _ in range(25):
            d = lc_profile(rng, N); r = F(rng.randint(1, 19), 20)
            Rs = [d[i] / (d[i + 1] - d[i]) for i in range(N)]
            if any(Rs[i + 1] < Rs[i] for i in range(N - 1)): bad('R mono')
            Rr = d[N - 1] / (1 - d[N - 1])
            tmax = (1 - r) / (N + Rr)
            for t, tau in [(tmax, F(0)), (tmax * F(rng.randint(0, 10), 10), None)]:
                if tau is None:
                    # quadratic: choose tau with equality in (2)
                    tau = ((1 - r) - t * (N + Rr)) / (F(N * (N - 1), 2) + (N - 1) * Rr)
                rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
                c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
                incs = [b[i + 1] - b[i] for i in range(N)]
                if min(incs) < 0: bad('b mono at max', (N, float(min(incs))))
                # just beyond: last increment negative
                n_arr += 1
                if tau == 0:
                    # key inequality (6)/(16) at all sources, alpha >= t u0/u1
                    for l in range(N + 1):
                        for a in range(3, N + 1 - l):
                            n_src += 1
                            u = [dif(d, n, l) for n in range(a + 2)] if l + a + 1 <= N else [dif(d, n, l) for n in range(a + 1)] + [F(0)]
                            al = 1 - r - t * (l + a)
                            if al < t * u[0] / u[1]: bad('(3)', (N, l, a))
                            fc = lambda n, ll: dif(c, n, ll)
                            B0 = sum(C(a, n) * fc(n, l) for n in range(2, a + 1)); B0p = sum(C(a - 1, j) * fc(j, l + 1) for j in range(2, a))
                            A0 = b[l + a] - b[l]; A0pp = b[l + a - 1] - b[l + 1]
                            H1 = sum((n - 2) * C(a, n) * (1 - rho(l + n)) * u[n] for n in range(3, a + 1))
                            V1 = sum((n - 2) * C(a, n) * n * t * u[n - 1] for n in range(3, a + 1))
                            if A0 * B0p + B0 * A0pp < c[l + 1] * (4 * H1 - 2 * V1): bad('(16)', (N, l, a))
                    if fails.get('(16)', 0) == 0 and N <= 8:
                        if first_negative(linearization(a_, b, c)): bad('(P) tau=0', N)
                else:
                    # (c) detours with the stated constants
                    for l in range(N + 1):
                        for a in range(2, N + 1 - l):
                            cc = c[l + 1] if l + 1 <= N else None
                            if cc is None: continue
                            fc = lambda n, ll: dif(c, n, ll)
                            B0 = sum(C(a, n) * fc(n, l) for n in range(2, a + 1))
                            fF = lambda n, ll: dif(d, n, ll) if n >= 0 else F(0)
                            h = lambda n, ll: (1 - rho(ll + n)) * fF(n, ll)
                            v = lambda n, ll: n * (t + tau * (ll + n - 1)) * fF(n - 1, ll)
                            w = lambda n, ll: C(n, 2) * tau * fF(n - 2, ll)
                            W = lambda s, p, qq, ll, aa: sum(C(nn - p + qq, qq) * C(aa, nn) * s(nn, ll) for nn in range(p, aa + 1))
                            for j in range(1, N + 1):
                                if a < 2 * j + 1: break
                                for name, mu, s, p0, q0 in [('H', 10, h, 1, 0), ('V', F(9, 2), v, 1, 0), ('W', 3, w, 1, 0), ('C', 6, fF, 2, 1)]:
                                    if name != 'C' and j < 2: continue
                                    P = 2 * j + p0 if name != 'C' else 2 * j + 2; Qj = j if name != 'C' else j + 1
                                    Pm = 2 * (j - 1) + (1 if name != 'C' else 2); Qm = (j - 1) if name != 'C' else j
                                    if a < P: continue
                                    if mu * cc * W(s, P, Qj, l, a) > B0 * W(s, Pm, Qm, l + 1, a - 2): bad('detour ' + name, (N, l, a, j))
    print('arrays', n_arr, 'sources', n_src, fails, flush=True)
    # (d) example and quadratic-profile subclass
    N = 4; d = [F(2 ** i - 1, 15) for i in range(5)]; r = F(1, 2); t = F(1, 10)
    c = [(r + t * i) * d[i] for i in range(5)]; b = [d[i] - c[i] for i in range(5)]; a_ = [1 - x for x in d]
    print('example b', [str(x) for x in b], 'neg', first_negative(linearization(a_, b, c)), 'Mmin', float(Mmin(a_, b, c)[0]))
    nq = 0
    for N in range(3, 9):
        for _ in range(12):
            n1 = F(1); n2 = F(rng.randint(0, 50), rng.choice([1, 10, 100]))
            D = [n1 * i + n2 * C(i, 2) for i in range(N + 1)]; d = [x / D[N] for x in D]
            r = F(rng.randint(1, 19), 20); Rr = d[N - 1] / (1 - d[N - 1])
            t = (1 - r) / (N + Rr) * F(rng.randint(0, 10), 10)
            tau = ((1 - r) - t * (N + Rr)) / (F(N * (N - 1), 2) + (N - 1) * Rr) * F(rng.randint(1, 10), 10)
            rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
            c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
            if first_negative(linearization(a_, b, c)): bad('(P) quadprofile', N)
            if Mmin(a_, b, c)[0] < 0: bad('M quadprofile', N)
            nq += 1
    print('quadratic profiles', nq, 'final fails', fails)
