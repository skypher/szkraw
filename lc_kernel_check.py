"""Exact diagnostics for Section 8 (Theorem 8.1, Lemmas 8.2-8.4) of paper.tex: the log-concave Newton criterion.
(1) f_i(r) f_l(r+1) >= D_{r+1} f_{i+l}(r) for i, l >= 1, f_i(r) = sum_h C(r,h) sigma_{i+h} (sigma_0 = 0).
(2) For every j >= 1 (absent moves weight 0), with A_j = W_{2j+1,j}, B_j = W_{2j+2,j}, C_j = W_{2j+2,j+1}:
    A_0(r,a) B_{j-1}(r+1,a-1) + B_0(r,a) A_{j-1}(r+1,a-2) >= 4 D_{r+1} A_j(r,a)
    B_0(r,a) B_{j-1}(r+1,a-2) >= 4 D_{r+1} B_j(r,a)
    B_0(r,a) C_{j-1}(r+1,a-2) >= 4 D_{r+1} C_j(r,a)
(3) Operator inequality P^2 >= 4Q entrywise on Omega_N (moves normalized by D at the destination), and the induction
    invariant c >= (1/2) P c, c >= 0 node by node, with the full closed-form recurrence (P = all even groups, Q = odd)."""
import sys, random
from fractions import Fraction as F
from math import comb
def lc_sigma(rng, K, zero_tail=True):
    x = [F(rng.choice([0, 1, 2, 5, 10, 50]), rng.choice([1, 10, 100])) for _ in range(K-1)]
    rho = [sum(x[i:]) for i in range(K-1)]
    s = [F(0), F(1)]
    for k in range(K-1): s.append(s[-1]*rho[k])
    return s
def make(s):
    K = len(s) - 1
    sig = lambda k: s[k] if 0 <= k <= K else F(0)
    f = lambda i, r: sum(comb(r, h)*sig(i + h) for h in range(0, r + 1)) if r >= 0 else F(0)
    D = lambda r: f(0, r)
    def W(p, q, r, a):
        if r < 0 or a < 0: return F(0)
        return sum(comb(n - p + q, q)*comb(a, n)*f(n, r) for n in range(p, a + 1))
    return sig, f, D, W
rng = random.Random(11)
bad1 = bad2 = n1 = n2 = 0
for trial in range(60):
    K = rng.choice([3, 4, 5, 6, 8, 12])
    s = lc_sigma(rng, K)
    sig, f, D, W = make(s)
    for r in range(0, 9):
        for i in range(1, 7):
            for l in range(1, 7):
                n1 += 1
                if f(i, r)*f(l, r+1) < D(r+1)*f(i+l, r): bad1 += 1
    A = lambda j, r, a: W(2*j+1, j, r, a); B = lambda j, r, a: W(2*j+2, j, r, a); C = lambda j, r, a: W(2*j+2, j+1, r, a)
    for j in range(1, 5):
        for r in range(0, 7):
            for a in range(0, 14):
                n2 += 3
                if A(0, r, a)*B(j-1, r+1, a-1) + B(0, r, a)*A(j-1, r+1, a-2) < 4*D(r+1)*A(j, r, a): bad2 += 1
                if B(0, r, a)*B(j-1, r+1, a-2) < 4*D(r+1)*B(j, r, a): bad2 += 1
                if B(0, r, a)*C(j-1, r+1, a-2) < 4*D(r+1)*C(j, r, a): bad2 += 1
print(f'(1): {n1} checks, {bad1} failures;  (2): {n2} checks, {bad2} failures', flush=True)
# control: non-LC sigma should break (1) or (2) somewhere
s = [F(0), F(1), F(0), F(0), F(1, 100)]
sig, f, D, W = make(s)
viol = sum(1 for r in range(0, 6) for i in range(1, 5) for l in range(1, 5) if f(i, r)*f(l, r+1) < D(r+1)*f(i+l, r))
print(f'control sigma=(1,0,0,1/100): violations of (1): {viol}', flush=True)

# (3) operator inequality and invariant on Omega_N with the full closed-form recurrence (t as polynomial)
def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def psc(p, c): return [c*x for x in p]
def nonneg(p): return all(x >= 0 for x in p)
def moves(s, N):
    """list of (source, target, weight-polynomial-in-t, parity) normalized by D at destination; parity 0 = even group (P), 1 = odd (Q)."""
    sig, f, D, W = make(s); out = []
    for r in range(0, N+1):
        for a in range(0, N+1 - r):
            for j in range(0, N+1):
                for (dr, da, wt, tpow) in ((j+1, -(2*j+1), W(2*j+1, j, r, a), 1), (j+1, -(2*j+2), W(2*j+2, j, r, a), 0), (j+2, -(2*j+2), W(2*j+2, j+1, r, a), 0)):
                    rt, at = r + dr, a + da
                    if at < 0 or rt + at > N or wt == 0: continue
                    poly = [F(0)]*tpow + [wt/D(rt)]
                    out.append(((r, a), (rt, at), poly, j % 2))
    return out
def pmul(p, q):
    o = [F(0)]*(len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for k, y in enumerate(q): o[i+k] += x*y
    return o
for trial in range(8):
    N = rng.choice([6, 8, 10])
    s = lc_sigma(rng, rng.choice([4, 6, N]))
    mv = moves(s, N)
    P = {}; Q = {}
    for src, tgt, w, par in mv:
        (Q if par else P).setdefault((src, tgt), [])
        d = Q if par else P
        d[(src, tgt)] = padd(d[(src, tgt)], w)
    P2 = {}
    for (x, y), w1 in P.items():
        for (y2, z2), w2 in P.items():
            if y2 == y:
                P2[(x, z2)] = padd(P2.get((x, z2), []), pmul(w1, w2))
    viol = sum(1 for k, q in Q.items() if not nonneg(padd(P2.get(k, []), psc(q, -4))))
    print(f'N={N} sigma={[str(x) for x in s[1:6]]}...: {len(Q)} Q entries, P^2 >= 4Q violations: {viol}', flush=True)

# Lemma 8.2 and the reduction: run recurrence (8.1) at t = (1-r)/sqrt(r) for r with rational square root, rebuild
# g(m,n;k) = r^((m+n-k)/2) e_k L_{mn}^k/(e_m e_n) from the kernel, and compare with direct linearization (probe.py).
from probe import linearization
def kernel_g(dprof, r, sr):
    N = len(dprof) - 1; t = (1 - r)/sr
    nu = [F(0)] + [sum((-1)**(k - i)*comb(k, i)*dprof[i] for i in range(k + 1)) for k in range(1, N + 1)]
    fv = lambda n, l: sum(comb(l, h)*(nu[n + h] if n + h <= N else 0) for h in range(0, l + 1))
    W = lambda p, q, l, a: F(0) if (l < 0 or a < 0) else sum(comb(n - p + q, q)*comb(a, n)*fv(n, l) for n in range(p, a + 1))
    dd = lambda i: sum(comb(i, k)*nu[k] for k in range(1, N + 1))
    e = [F(1)]
    for i in range(N): e.append(e[-1]*(1 - dprof[i])/dprof[i + 1])
    G = [[[F(0)]*(N + 1) for _ in range(N + 1)] for _ in range(N + 1)]
    for k in range(N + 1):
        om = {(0, k): F(1)}
        o = lambda l, a: om.get((l, a), F(0))
        for l in range(0, N):
            for a in range(0, N + 1 - (l + 1)):
                v = (1 - dd(l + a))*o(l, a)
                for j in range(0, N + 1):
                    sgn = (-1)**j
                    v += sgn*(t*W(2*j+1, j, l-j, a+2*j+1)*o(l-j, a+2*j+1) + W(2*j+2, j, l-j, a+2*j+2)*o(l-j, a+2*j+2)
                              + W(2*j+2, j+1, l-j-1, a+2*j+2)*o(l-j-1, a+2*j+2))
                om[(l + 1, a)] = v/dd(l + 1)
        for m in range(N + 1):
            for n in range(N + 1):
                Lmn = sum(om.get((l, m + n - 2*l), F(0))*comb(m + n - 2*l, m - l) for l in range(0, min(m, n) + 1))
                s2 = m + n - k
                fac = (sr**s2) if s2 >= 0 else 1/(sr**(-s2))
                G[m][n][k] = fac*e[k]*Lmn/(e[m]*e[n])
    return G
bad = tot = 0
for trial in range(12):
    N = rng.choice([3, 4, 5, 6, 7])
    s = lc_sigma(rng, rng.choice([2, 3, N]))
    D = [sum(comb(i, k)*(s[k] if k < len(s) else 0) for k in range(1, i + 1)) for i in range(N + 1)]
    dprof = [x/D[N] for x in D]
    for r, sr in ((F(1, 4), F(1, 2)), (F(4, 9), F(2, 3)), (F(1), F(1))):
        Gk = kernel_g(dprof, r, sr)
        Gd = linearization([1 - x for x in dprof], [(1 - r)*x for x in dprof], [r*x for x in dprof])
        for m in range(N + 1):
            for n in range(N + 1):
                for k in range(N + 1):
                    tot += 1
                    if Gk[m][n][k] != Gd[m][n][k]: bad += 1
print(f'Lemma 8.2 and reduction: {tot} coefficients g(m,n;k) from the kernel recurrence vs direct linearization, {bad} mismatches', flush=True)
