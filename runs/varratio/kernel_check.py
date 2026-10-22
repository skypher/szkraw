"""Exact check of the varying-ratio kernel recurrence in the paper's stochastic normalization.
Array: a + b + c = 1, b_0 = c_0 = 0, a_N = 0; c_n = sum C(n,k) nu_k, b_n = sum C(n,k) beta_k.
E_i = e_i R_i with e_{i+1}/e_i = a_i / c_{i+1}; generator L_z = z^-1 c(th) + b(th) + z(1 - b(th) - c(th)).
Recurrence: c_{l+1} om[l+1,a] = a_{l+a} om[l,a] + sum_j (-1)^j ( Ab_j(l-j,a+2j+1) om[l-j,a+2j+1]
            + B_j(l-j,a+2j+2) om[l-j,a+2j+2] + (C_j + Cb_j)(l-j-1,a+2j+2) om[l-j-1,a+2j+2] ),
with B_j = W^nu_{2j+2,j}, C_j = W^nu_{2j+2,j+1}, Ab_j = W^beta_{2j+1,j}, Cb_j = W^beta_{2j+2,j+1}.
Checks: (I) g(m,n;k) rebuilt from the kernel equals direct linearization (probe.py), for arbitrary b, c;
(II) on members of criterion S: all moves nonnegative, P^2 >= 4Q entrywise (moves normalized by c at the destination),
and the local inequalities (a), (b), (c)."""
import sys, random, math
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization
from mixed import newton_coeffs
import stoch

def tools(b, c):
    N = len(c) - 1
    nu = newton_coeffs(c) + [F(0)] * (2 * N + 4)
    be = newton_coeffs(b) + [F(0)] * (2 * N + 4)
    f = lambda s, n, l: sum(comb(l, h) * s[n + h] for h in range(l + 1)) if l >= 0 else F(0)
    def W(s, p, q, l, a):
        if l < 0 or a < 0: return F(0)
        return sum(comb(n - p + q, q) * comb(a, n) * f(s, n, l) for n in range(p, a + 1))
    cpol = lambda i: f(nu, 0, i); bpol = lambda i: f(be, 0, i)
    return nu, be, f, W, cpol, bpol

def kernel_g(a_, b, c):
    N = len(c) - 1
    nu, be, f, W, cpol, bpol = tools(b, c)
    apol = lambda i: 1 - bpol(i) - cpol(i)
    e = [F(1)]
    for i in range(N): e.append(e[-1] * a_[i] / c[i + 1])
    G = [[[F(0)] * (N + 1) for _ in range(N + 1)] for _ in range(N + 1)]
    for k in range(N + 1):
        om = {(0, k): F(1)}
        o = lambda l, a: om.get((l, a), F(0))
        for l in range(0, N):
            for a in range(0, N + 1 - (l + 1)):
                v = apol(l + a) * o(l, a)
                for j in range(0, N + 1):
                    v += (-1) ** j * (W(be, 2*j+1, j, l-j, a+2*j+1) * o(l-j, a+2*j+1)
                                      + W(nu, 2*j+2, j, l-j, a+2*j+2) * o(l-j, a+2*j+2)
                                      + (W(nu, 2*j+2, j+1, l-j-1, a+2*j+2) + W(be, 2*j+2, j+1, l-j-1, a+2*j+2)) * o(l-j-1, a+2*j+2))
                om[(l + 1, a)] = v / cpol(l + 1)
        for m in range(N + 1):
            for n in range(N + 1):
                L = sum(om.get((l, m + n - 2*l), F(0)) * comb(m + n - 2*l, m - l) for l in range(0, min(m, n) + 1))
                G[m][n][k] = e[k] * L / (e[m] * e[n])
    return G

def operator_check(b, c):
    N = len(c) - 1
    nu, be, f, W, cpol, bpol = tools(b, c)
    P = {}; Q = {}; neg = 0
    for l in range(0, N + 1):
        for a in range(0, N + 1 - l):
            for j in range(0, N + 1):
                for (dl, da, wt) in ((j+1, -(2*j+1), W(be, 2*j+1, j, l, a)), (j+1, -(2*j+2), W(nu, 2*j+2, j, l, a)),
                                     (j+2, -(2*j+2), W(nu, 2*j+2, j+1, l, a) + W(be, 2*j+2, j+1, l, a))):
                    lt, at = l + dl, a + da
                    if at < 0 or lt + at > N or wt == 0: continue
                    if wt < 0: neg += 1
                    d = Q if j % 2 else P
                    d[((l, a), (lt, at))] = d.get(((l, a), (lt, at)), F(0)) + wt / cpol(lt)
    P2 = {}
    for (x, y), w1 in P.items():
        for (y2, z), w2 in P.items():
            if y2 == y: P2[(x, z)] = P2.get((x, z), F(0)) + w1 * w2
    viol = sum(1 for kk, q in Q.items() if P2.get(kk, F(0)) < 4 * q)
    return neg, len(Q), viol

if __name__ == '__main__':
    rng = random.Random(5)
    # (I) arbitrary b, c (Newton-nonneg not required): recurrence identity
    bad = tot = 0
    for trial in range(40):
        N = rng.choice([2, 3, 4, 5, 6])
        c = [F(0)] + sorted(F(rng.randint(1, 100), 100) for _ in range(N))
        b = [F(0)] + [F(rng.randint(0, 100), 300) for _ in range(N)]
        s = b[N] + c[N]; b = [x / s for x in b]; c = [x / s for x in c]
        a_ = [1 - x - y for x, y in zip(b, c)]
        if any(x <= 0 for x in a_[:N]): continue
        Gk = kernel_g(a_, b, c); Gd = linearization(a_, b, c)
        for m in range(N + 1):
            for n in range(N + 1):
                for k in range(N + 1):
                    tot += 1
                    if Gk[m][n][k] != Gd[m][n][k]: bad += 1
    print(f'(I) kernel recurrence vs direct linearization (arbitrary arrays): {tot} coefficients, {bad} mismatches', flush=True)
    # (II) criterion S members (w nonincreasing): moves, P^2 >= 4Q
    tq = tv = tn = 0
    for trial in range(40):
        N = rng.choice([4, 6, 8, 10])
        a_, b, c = stoch.member(rng, N, 'M')
        neg, nq, viol = operator_check(b, c)
        tn += neg; tq += nq; tv += viol
    print(f'(II) criterion S (w nonincreasing), N in 4..10: {tq} Q entries, P^2 >= 4Q violations {tv}, negative move weights {tn}', flush=True)
    # control: spike members violating the mixed inequalities
    from mixed import mixed_ok
    cv = cq = 0
    for trial in range(200):
        a_, b, c = stoch.member(rng, rng.choice([3, 4, 5]), 'spike')
        if mixed_ok(b, c): continue
        neg, nq, viol = operator_check(b, c); cv += viol; cq += nq
    print(f'control (spike, mixed inequalities violated): {cq} Q entries, P^2 >= 4Q violations {cv}', flush=True)
