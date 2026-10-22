"""Node-by-node exact check of the general kernel recurrence (closed form, all groups G_j) on full-degree profiles:
(a) the recurrence reproduces the true L_{mn}^k (validates the closed form at degree N);
(b) c >= 0; (c) half-inflow hypothesis D_r c_{r,a} >= (1/2)(G_0 inflow) at every node;
(d) margin of the odd-group demand: sum of G_{2j+1} jumps into the node vs half of G_0 inflow."""
import sys, random
from fractions import Fraction as F
from math import comb
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables, padd, psc, ptm
def pe(p, q): n = max(len(p), len(q)); return all((p[i] if i < len(p) else 0) == (q[i] if i < len(q) else 0) for i in range(n))
def nonneg(p): return all(x >= 0 for x in p)
def run(sig, N, check_L=True):
    K = len(sig)                                   # sig[0] = sigma_1 = 1
    s = [F(0)] + list(sig)
    Dn = lambda n: sum(comb(n, k)*s[k] for k in range(1, min(n, K)+1)) if n >= 0 else F(0)
    T = Dn(N)
    def W(i, j, r, a):
        if r < 0 or a < 0: return F(0)
        return sum(comb(ip - i + j, j)*comb(a, ip)*comb(r, jp)*s[ip + jp] for ip in range(i, min(a, K)+1) for jp in range(0, min(r, K-ip)+1) if ip + jp >= 1)
    H = None
    if check_L:
        d = [Dn(i)/T for i in range(N+1)]; H, _ = tables(d)
        A = [F(1)]
        for j in range(1, N+1): A.append(A[-1]*Dn(j))
        Q = [F(1)]
        for j in range(N): Q.append(Q[-1]*(T - Dn(j)))
        e = [Q[r]/A[r] for r in range(N+1)]
    st = {'L': 0, 'neg': 0, 'half': 0, 'margin': None}
    for k in range(N+1):
        c = {(0, k): [F(1)]}
        g = lambda r, a: c.get((r, a), [])
        for r in range(0, N+1):
            for a in range(0, N + 2):
                tot = psc(g(r, a), T - Dn(r + a)); G0 = []; odd = []
                for j in range(0, N):
                    terms = [(ptm(g(r-j, a+2*j+1)), W(2*j+1, j, r-j, a+2*j+1)),
                             (g(r-j, a+2*j+2), W(2*j+2, j, r-j, a+2*j+2)),
                             (g(r-j-1, a+2*j+2), W(2*j+2, j+1, r-j-1, a+2*j+2))]
                    grp = []
                    for p_, wt in terms:
                        if p_ and wt: grp = padd(grp, psc(p_, wt))
                    if not grp: continue
                    if j % 2 == 0: tot = padd(tot, grp)
                    else: tot = padd(tot, psc(grp, -1)); odd = padd(odd, grp)
                    if j == 0: G0 = grp
                if not any(tot): continue
                c[(r+1, a)] = psc(tot, 1/Dn(r+1))
                if not nonneg(c[(r+1, a)]): st['neg'] += 1
                if not nonneg(padd(tot, psc(G0, F(-1, 2)))): st['half'] += 1
                if any(odd):
                    # margin: min over t-powers of (1/2 G0) / odd
                    for i, o in enumerate(odd):
                        if o > 0:
                            m = (G0[i]/2 if i < len(G0) else 0)/o
                            if st['margin'] is None or m < st['margin']: st['margin'] = m
        if check_L:
            for m in range(N+1):
                for n in range(N+1):
                    Lt = []
                    for r in range(0, min(m, n) + 1):
                        aa = m + n - 2*r
                        Lt = padd(Lt, psc(c.get((r, aa), []), comb(aa, m - r)))
                    if not pe(Lt, psc(H[m][n][k], e[m]*e[n]/e[k])): st['L'] += 1
    return st
if __name__ == '__main__':
    rng = random.Random(4)
    def lc_sig(N, rho):
        s = [F(1)]
        for x in rho[:N-1]: s.append(s[-1]*x)
        return s
    for N in (6, 8, 10, 12):
        cases = [('geometric 1/10', lc_sig(N, [F(1, 10)]*(N-1))), ('geometric 1', lc_sig(N, [F(1)]*(N-1))),
                 ('LC random', lc_sig(N, sorted([F(rng.randint(1, 30), 10) for _ in range(N-1)], reverse=True))),
                 ('LC two-level', lc_sig(N, [F(1, 2)]*(N//2) + [F(1, 20)]*(N - 1 - N//2))),
                 ('log-convex', lc_sig(N, sorted([F(rng.randint(1, 30), 10) for _ in range(N-1)]))),
                 ('internal zero', [F(1), F(0), F(0), F(1, 100)] + [F(0)]*(N-4))]
        for name, sig in cases:
            st = run(sig, N, check_L=(N <= 10))
            m = st['margin']
            print(f'N={N} {name:15s}: L mismatches {st["L"]}, negative c {st["neg"]}, half-inflow failures {st["half"]}, '
                  f'min (G0/2)/odd {float(m) if m is not None else None}', flush=True)
