"""Exact certificate that a profile violating log-concavity of its Newton coefficients by a factor 1/mu still has (P)
for every r in [0, 1]. Profile D(i) = (1 - mu) i + mu [i]_q (Newton ratios mu(q-1), q-1, q-1, ...: one upward step by
the factor 1/mu), d = D / D(N), constant ratio a = 1 - d, b = (1-r) d, c = r d. Every g(m,n;k) is a polynomial in r
(divisions only by a_m); (P) on [0,1] follows if all its Bernstein coefficients are >= 0; otherwise the polynomial is
checked exactly for a sign change on (0,1] (Sturm). Usage: lc_violation_cert.py N mu q"""
import sys
from fractions import Fraction as F
import sympy as sp
N, mu, q = int(sys.argv[1]), F(sys.argv[2]), F(sys.argv[3])
D = [(1 - mu) * i + mu * sum(q ** j for j in range(i)) for i in range(N + 1)]
d = [x / D[N] for x in D]; a = [1 - x for x in d]
sig = [sum((-1) ** (k - i) * sp.binomial(k, i) * D[i] for i in range(k + 1)) for k in range(1, N + 1)]
viol = max(F(int(sp.numer(sig[k + 1] * sig[k - 1])), 1) / F(int(sp.numer(sig[k] ** 2)), 1) * 0 + (sig[k + 1] * sig[k - 1]) / (sig[k] ** 2) for k in range(1, N - 1))
def padd(p, q_):
    n = max(len(p), len(q_)); return [(p[i] if i < len(p) else 0) + (q_[i] if i < len(q_) else 0) for i in range(n)]
def pscale(p, c): return [c * x for x in p]
def pmul_lin(p, c0, c1):  # p * (c0 + c1 r)
    out = [F(0)] * (len(p) + 1)
    for i, x in enumerate(p): out[i] += c0 * x; out[i + 1] += c1 * x
    return out
size = N + 1
cur = [[[F(int(i == j))] for j in range(size)] for i in range(size)]; prev = [[[F(0)] for _ in range(size)] for _ in range(size)]
tables = [cur]
for m in range(N):
    nxt = []
    for i in range(size):
        row = []
        for j in range(size):
            v = pmul_lin(cur[i][j], d[i] - d[m], -(d[i] - d[m]))          # (b_i - b_m) = (1 - r)(d_i - d_m)
            v = padd(v, pmul_lin(prev[i][j], F(0), -d[m]))                # - c_m prev
            if i: v = padd(v, pmul_lin(cur[i - 1][j], F(0), d[i]))       # + c_i cur[i-1]
            if i < N: v = padd(v, pscale(cur[i + 1][j], a[i]))           # + a_i cur[i+1]
            row.append(pscale(v, 1 / a[m]))
        nxt.append(row)
    prev, cur = cur, nxt; tables.append(cur)
r = sp.Symbol('r'); nonbern = 0; bad = []
for m, T in enumerate(tables):
    for n_, row in enumerate(T):
        for k, p in enumerate(row):
            while len(p) > 1 and p[-1] == 0: p = p[:-1]
            deg = len(p) - 1
            bern = [sum(F(sp.binomial(i, j)) / F(sp.binomial(deg, j)) * p[j] for j in range(i + 1)) for i in range(deg + 1)]
            if min(bern) >= 0: continue
            nonbern += 1
            P = sp.Poly([sp.Rational(x.numerator, x.denominator) for x in reversed(p)], r)
            if P.eval(0) < 0 or P.eval(1) < 0 or P.count_roots(0, 1) > 0 and any(P.eval(sp.Rational(x)) < 0 for x in [sp.nsimplify(rt) for rt in []]):
                bad.append((m, n_, k))
            else:
                # exact: sign at midpoints between real roots in (0,1)
                rts = sorted(set([0, 1] + [x for x in sp.Poly(P).real_roots() if 0 < x < 1]), key=lambda x: float(x))
                for lo, hi in zip(rts, rts[1:]):
                    mid = sp.Rational(sp.nsimplify((sp.N(lo, 50) + sp.N(hi, 50)) / 2, rational=True))
                    if P.eval(mid) < 0: bad.append((m, n_, k)); break
print(f'N = {N}, mu = {mu}, q = {q}: max Newton log-convexity factor sigma_(k-1) sigma_(k+1) / sigma_k^2 = {float(viol):.6g}')
print(f'entries without nonnegative Bernstein form: {nonbern}; entries negative somewhere on [0,1]: {len(bad)} {bad[:5]}')
print('CERTIFIED: (P) for every r in [0,1]' if not bad else 'FAILS')
