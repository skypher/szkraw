"""The symmetric endpoint K(N,1): interior directions for every N (Section 8); exact diagnostics.

Measure coordinates: a finite system is its orthogonality measure (nodes x_0 > ... > x_N, weights w_j), with
R_n normalized by R_n(x_0) = 1. Product coefficients are invariant under affine changes of x.

1. Top-mass lemma (proof in RESEARCH.md): for mu_eps = mu - eps*delta_{x_0}, at a zero of int R_x R_y R_z dmu,
   d/d eps int R_x R_y R_z dmu_eps = 2 - [T_x(y,z) + T_y(x,z) + T_z(x,y)], with T_x(y,z) = sum_{k>=x} g(y,z;k).
   Checked exactly at every structural zero of K(N,1), N <= 8.
2. Boolean formula g(m,n;k) = sum_j H(m,n;j) C(j,s) r^(j-s) (1-r)^s, s = k-m-n+2j, for K(N,r).
3. Interior: lowering the top mass by eps and r by Lambda*eps makes every triangle coefficient strictly positive
   once Lambda exceeds an explicit Lambda_N (checked exactly for N <= 12).
4. In recurrence coefficients, lowering the top mass of any finite system changes (a_n, b_n, c_n) at rate
   pi_n (a_n, c_n - a_n, -c_n) (proof in RESEARCH.md); for K(N,1) this is
   dc_n = -C(N-1,n-1), db_n = -C(N,n)(N-2n)/N. Checked on K(N,1), N <= 12, and on random measures.
"""
import argparse
from fractions import Fraction as F
from math import comb
from probe import linearization
from szwarc_check import geometric

def recurrence_from_measure(x, w):
    """Stieltjes procedure on node values; returns (a, b, c) with R_n(x[0]) = 1."""
    M = len(x)
    ip = lambda f, g: sum(wi*fi*gi for wi, fi, gi in zip(w, f, g))
    P_prev = [F(0)]*M; P = [F(1)]*M
    beta, lam, vals = [], [F(0)], [P[0]]
    for n in range(M):
        nn = ip(P, P)
        beta.append(ip([xi*p for xi, p in zip(x, P)], P)/nn)
        if n == M-1: break
        P_next = [(xi - beta[n])*p - lam[n]*pp for xi, p, pp in zip(x, P, P_prev)]
        lam.append(ip(P_next, P_next)/nn)
        P_prev, P = P, P_next
        vals.append(P[0])
    N = M-1
    a = [vals[n+1]/vals[n] if n < N else F(0) for n in range(M)]
    c = [lam[n]*vals[n-1]/vals[n] if n > 0 else F(0) for n in range(M)]
    return a, beta, c

def kraw_measure(N, r):
    p0 = r/(1+r)
    return [1 - (1+r)*F(j, N) for j in range(N+1)], [comb(N, j)*p0**(N-j)*(1-p0)**j for j in range(N+1)]

def zeros(N):
    g = linearization(*recurrence_from_measure(*kraw_measure(N, F(1))))
    return [(p, q, s) for p in range(N+1) for q in range(p, N+1) for s in range(q, min(p+q, N)+1) if g[p][q][s] == 0], g

TINY = F(1, 10**30)

def top_rates(N):
    x, w = kraw_measure(N, F(1)); w[0] -= TINY
    g = linearization(*recurrence_from_measure(x, w))
    return lambda p: g[p[0]][p[1]][p[2]]/TINY

def kraw_rates(N):
    g = linearization(*recurrence_from_measure(*kraw_measure(N, 1 - TINY)))
    return lambda p: g[p[0]][p[1]][p[2]]/TINY

def check_top_lemma(N):
    Z, g = zeros(N); rate = top_rates(N)
    for (x, y, z) in Z:
        tails = (sum(g[y][z][k] for k in range(x, N+1)) + sum(g[x][z][k] for k in range(y, N+1))
                 + sum(g[x][y][k] for k in range(z, N+1)))
        if abs(rate((x, y, z)) - comb(N, z)*(2 - tails)) > F(1, 10**25): return False
    return True

def boolean(N, r, m, n, k):
    tot = F(0)
    for j in range(max(0, m+n-N), min(m, n)+1):
        s = k - m - n + 2*j
        if 0 <= s <= j:
            tot += F(comb(m, j)*comb(N-m, n-j), comb(N, n))*comb(j, s)*r**(j-s)*(1-r)**s
    return tot

def interior(N):
    Z, _ = zeros(N); top, kr = top_rates(N), kraw_rates(N)
    lam_N = max([F(0)] + [-top(p)/kr(p) for p in Z if top(p) < 0])
    Lam, eps = 2*lam_N + 1, F(1, 10**12)
    x, w = kraw_measure(N, 1 - Lam*eps); w[0] -= eps
    g = linearization(*recurrence_from_measure(x, w))
    mn = min(g[a][b][c] for a in range(N+1) for b in range(a, N+1) for c in range(abs(a-b), min(a+b, N)+1))
    return lam_N, mn

def top_in_recurrence(N):
    x, w = kraw_measure(N, F(1))
    a0, b0, c0 = recurrence_from_measure(x, w)
    w2 = list(w); w2[0] -= TINY
    a1, b1, c1 = recurrence_from_measure(x, w2)
    db_ok = all(abs((b1[n]-b0[n])/TINY + F(comb(N, n)*(N-2*n), N)) < F(1, 10**20) for n in range(N+1))
    dc_ok = all(abs((c1[n]-c0[n])/TINY + (comb(N-1, n-1) if n else 0)) < F(1, 10**20) for n in range(N+1))
    return db_ok and dc_ok

def top_formula_random(seed=4, trials=6):
    from random import Random
    rng = Random(seed); worst = F(0)
    for _ in range(trials):
        N = rng.choice([3, 5, 7, 9])
        x = sorted({F(rng.randint(-100, 100), 37) for _ in range(3*N)}, reverse=True)[:N+1]
        w = [F(rng.randint(1, 50)) for _ in range(len(x))]
        N = len(x) - 1
        a, b, c = recurrence_from_measure(x, w)
        pi = [1/sum(w)]
        for n in range(N): pi.append(pi[-1]*a[n]/c[n+1])
        w2 = list(w); w2[0] -= TINY
        a1, b1, c1 = recurrence_from_measure(x, w2)
        worst = max([worst] + [max(abs((a1[n]-a[n])/TINY - pi[n]*a[n]), abs((b1[n]-b[n])/TINY - pi[n]*(c[n]-a[n])),
                                   abs((c1[n]-c[n])/TINY + pi[n]*c[n])) for n in range(N+1)])
    return worst

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    print('1. top-mass lemma exact at all structural zeros, N = 3..8:', all(check_top_lemma(N) for N in range(3, 9)), flush=True)
    ok = all(linearization(*geometric(N, F(1), r))[m][n][k] == boolean(N, r, m, n, k)
             for N in (3, 5, 7) for r in (F(1, 3), F(1, 2), F(1)) for m in range(N+1) for n in range(N+1) for k in range(N+1))
    print('2. Boolean formula exact for K(N,r), N = 3, 5, 7, r = 1/3, 1/2, 1:', ok, flush=True)
    for N in range(3, 13):
        lam_N, mn = interior(N)
        print(f'3. N={N}: Lambda_N = {float(lam_N):.6g}; all triangle coefficients > 0 at eps = 1e-12, Lambda = 2 Lambda_N + 1: {mn > 0}', flush=True)
    print('4. top-mass lowering = (db_n, dc_n) = (-C(N,n)(N-2n)/N, -C(N-1,n-1)), N = 2..12:',
          all(top_in_recurrence(N) for N in range(2, 13)), flush=True)
    print(f'4. general formula pi_n (a_n, c_n - a_n, -c_n) on random measures: max deviation {float(top_formula_random()):.1e} (step 1e-30)', flush=True)

if __name__ == '__main__':
    main()
