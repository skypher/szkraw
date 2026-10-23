"""Exact check of every step of Theorem Q on random members (bounded: N <= 10).
Profile d_i = nu1 i + nu2 C(i,2) (nu1 > 0, nu2 >= 0, d_N = 1); ratio rho with nonnegative log-concave Newton
coefficients (random degree, geometric = exponential ratio included); b nondecreasing (scale at the maximum or half).
Checks: (1) Newton(c) = k e_k with e_k = (nu1 + h(k-1)) s_k + h(k-1) s_{k-1}, s_k = rho_k + rho_{k-1}, h = nu2/2;
(2) Newton(c) nonnegative and log-concave without internal zeros; (3) lc-ineq for phi with i = 2;
(4) P^2/4 - Q >= 0; (5) Btilde detour B_0 Bt_{j-1}' >= 10 c Bt_j; (6) M = G(P^2/4 - Q + U + A0 + C0' + Bt_+ - Bt_-)G >= 0
via the recurrence's own moves (resum_test.Mmin); (7) property (P). Usage: thmQ_check.py Nmax per seed"""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
from resum_test import Mmin

def newton(seq): return [sum((-1) ** (k - i) * math.comb(k, i) * seq[i] for i in range(k + 1)) for k in range(len(seq))]
def lcnz(v):
    sup = [i for i, x in enumerate(v) if x > 0]
    return all(x >= 0 for x in v) and (not sup or sup == list(range(sup[0], sup[-1] + 1))) and \
        all(v[k] ** 2 >= v[k - 1] * v[k + 1] for k in range(1, len(v) - 1))

def member(rng, N):
    nu1 = F(1); nu2 = F(rng.choice([0, 0, 1, 2, 5, 20]), rng.choice([1, N]))
    D = [nu1 * i + nu2 * math.comb(i, 2) for i in range(N + 1)]; d = [x / D[N] for x in D]
    nu1, nu2 = nu1 / D[N], nu2 / D[N]
    r = F(rng.choice([1, 10, 30, 50, 80, 95, 99])) / 100
    vs = sorted((F(rng.randint(0, 20), 20) for _ in range(N)), reverse=True)
    if rng.random() < .3: vs = [F(1)] * N
    K = rng.randint(1, N)
    def cof(s):
        co = [r, s]
        for k in range(2, N + 1): co.append(co[-1] * (s / r) * vs[k - 2] if k <= K else F(0))
        return co
    def arr(co):
        rho = [sum(ck * math.comb(i, k) for k, ck in enumerate(co) if k <= i) for i in range(N + 1)]
        c = [x * y for x, y in zip(rho, d)]; b = [x - y for x, y in zip(d, c)]
        return [1 - x for x in d], b, c, rho
    def ok(s):
        a, b, c, rho = arr(cof(s)); return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(N))
    lo, hi = F(0), F(1)
    while ok(hi): hi *= 2
    for _ in range(30):
        mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    co = cof(lo * rng.choice([F(1), F(1, 2)]))
    return (nu1, nu2), co, arr(co)

if __name__ == '__main__':
    Nmax, per, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
    bad = {}; tot = 0
    for N in range(3, Nmax + 1):
        for _ in range(per):
            (nu1, nu2), co, (a, b, c, rho) = member(rng, N); tot += 1
            kap = newton(c); h = nu2 / 2
            s = [co[k] + (co[k - 1] if k >= 1 else 0) for k in range(N + 1)]
            e = [(nu1 + h * (k - 1)) * s[k] + h * (k - 1) * (s[k - 1] if k >= 1 else 0) for k in range(N + 1)]
            if any(kap[k] != k * e[k] for k in range(1, N + 1)): bad['formula'] = bad.get('formula', 0) + 1
            if not lcnz(kap[1:]): bad['NewtonLC'] = bad.get('NewtonLC', 0) + 1
            dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1))
            ce = [sum(kap[k] * math.comb(x, k) for k in range(N + 1)) for x in range(2 * N + 3)]  # polynomial extension
            phi = lambda n, l: dif(ce, n, l)
            for l in range(N):
                for n in range(1, N):
                    if phi(2, l) * phi(n, l + 1) < ce[l + 1] * phi(n + 2, l): bad['lcphi'] = bad.get('lcphi', 0) + 1
            W = lambda n0, p, q, l, a_: sum(math.comb(n - p + q, q) * math.comb(a_, n) * phi(n, l) for n in range(p, a_ + 1))
            for l in range(N):
                for a_ in range(N + 1 - l):
                    B0 = W(0, 2, 0, l, a_)
                    for j in range(1, N + 1):
                        if a_ < 2 * j + 1: break
                        if B0 * W(0, 2 * j, j - 1, l + 1, a_ - 2) < 4 * ce[l + 1] * W(0, 2 * j + 2, j, l, a_): bad['Bdet'] = bad.get('Bdet', 0) + 1
                        if j >= 2 and B0 * W(0, 2 * j - 1, j - 1, l + 1, a_ - 2) < 10 * ce[l + 1] * W(0, 2 * j + 1, j, l, a_): bad['Btdet'] = bad.get('Btdet', 0) + 1
            if Mmin(a, b, c)[0] < 0: bad['M'] = bad.get('M', 0) + 1
            if first_negative(linearization(a, b, c)): bad['P'] = bad.get('P', 0) + 1
        print(f"N={N}: {tot} arrays, failures {bad}", flush=True)
