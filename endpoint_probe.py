"""Polynomial-certificate probes near the symmetric endpoint (Section 8); diagnostics, not a proof.

In Szwarc's normalization (3.9) with sigma_n = r^(n/2), the Krawtchouk array becomes, after dividing by
sqrt r, x P_n = d_{n+1} P_{n+1} + t d_n P_n + (1 - d_{n-1}) P_{n-1} with t = 1/sqrt(r) - sqrt(r).
Only the diagonal depends on r, so every product coefficient is a polynomial in t. We study the
families (A, B, C) = (c_{n+1}, B_n, 1 - c_{n-1}) with c palindromic (c_n + c_{N-n} = 1, increasing):
B = 0 is the class of Corollary 7.15, and B = t c contains every Krawtchouk array (c_n = n/N).
Coefficients of (A, B, C) are positive multiples of those of its stochastic normalization, since
A_n, C_n > 0 make the recurrence polynomials positive at the top of the spectrum.

Checks (exact unless stated):
1. Krawtchouk: all t-coefficients are nonnegative, lowest power max(m+n+k-2N, parity).
2. Palindromic B = 0: g(x,y;z) = g(N-x,N-y;z), hence g = 0 when x+y+z > 2N, for every such c.
3. Free diagonal on the Krawtchouk off-diagonal part: a nondecreasing B can break (P) (N = 3).
4. B = t c: first-order conditions as t -> 0 (sympy): c_1 >= 1/N for N = 3, 4; 2c_1 >= c_2 for N = 5.
   Exact counterexamples: increments shrinking toward the middle (U-shaped) at N = 6, and
   concave decreasing half-increments at N = 14.
5. First-order tangent cone at Krawtchouk (in the drops d_n = -Laplacian of c at nodes n < N/2):
   LP ranges of d_s/d_{s+1} (need numpy and scipy) and exact membership of "flat start" rays.
6. Exact counterexample to the ratio hypothesis (d_n >= 0, d_n/(N/2-n) nondecreasing) at N = 11.
"""
import argparse
from fractions import Fraction as F
from probe import linearization

def padd(p, q, s=1):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + s*(q[i] if i < len(q) else 0) for i in range(n)]

def lin_poly(A, beta, C):
    """T[m][i][j]: coefficient of P_j in P_m P_i as a polynomial in t (list), for B = t*beta."""
    S = len(A)
    I = [[[F(int(i == j))] for j in range(S)] for i in range(S)]
    Z = [[[F(0)] for j in range(S)] for i in range(S)]
    res = [I]; prev, cur = Z, I
    for m in range(S-1):
        nxt = []
        for i in range(S):
            row = []
            for j in range(S):
                e = [0] + [(beta[i]-beta[m])*x for x in cur[i][j]]
                e = padd(e, prev[i][j], -C[m])
                if i: e = padd(e, cur[i-1][j], C[i])
                if i+1 < S: e = padd(e, cur[i+1][j], A[i])
                row.append([x/A[m] for x in e])
            nxt.append(row)
        res.append(nxt); prev, cur = cur, nxt
    return res

def base(c):
    N = len(c)-1
    return [c[i+1] if i < N else F(0) for i in range(N+1)], [1-c[i-1] if i > 0 else F(0) for i in range(N+1)]

def profile(inc):
    """Increasing profile with the given (positive) increments, scaled to c_N = 1."""
    c = [F(0)]
    for x in inc: c.append(c[-1]+x)
    return [x/c[-1] for x in c]

def palindromic(half, N):
    inc = [None]*N
    for i, x in enumerate(half): inc[i] = x; inc[N-1-i] = x
    return profile(inc)

def deep(N, x, y, z):
    return x+y > N and x+z > N and y+z > N

def check_krawtchouk(N):
    A, C = base([F(i, N) for i in range(N+1)])
    T = lin_poly(A, [F(i, N) for i in range(N+1)], C)
    neg = order = 0
    for m in range(N+1):
        for i in range(N+1):
            for j in range(N+1):
                p = T[m][i][j]
                neg += any(x < 0 for x in p)
                if deep(N, m, i, j):
                    low = next(l for l, x in enumerate(p) if x != 0)
                    order += low != max(m+i+j-2*N, (m+i+j) % 2)
    return neg, order

def check_mirror_zero(c):
    N = len(c)-1; A, C = base(c)
    g = linearization(A, [F(0)]*(N+1), C)
    mirror = all(g[x][y][z] == g[N-x][N-y][z] for x in range(N+1) for y in range(N+1) for z in range(N+1))
    perim = all(g[x][y][z] == 0 for x in range(N+1) for y in range(N+1) for z in range(N+1) if x+y+z > 2*N)
    return mirror, perim

def min_entry(c, B):
    A, C = base(c)
    g = linearization(A, B, C)
    N = len(c)-1
    return min((g[x][y][z], (x, y, z)) for x in range(N+1) for y in range(N+1) for z in range(N+1))

def scan_t(c, ts):
    """Most negative product coefficient of (A, t c, C) over the given t values."""
    return min((min_entry(c, [t*x for x in c]) + (t,) for t in ts), key=lambda v: v[0])

def first_order_symbolic():
    import sympy as sp
    t = sp.symbols('t')
    out = []
    for N in (3, 4, 5):
        k = (N-1)//2; cs = sp.symbols(f'c1:{k+1}')
        c = [sp.Integer(0)] + [None]*(N-1) + [sp.Integer(1)]
        for i in range(1, k+1): c[i] = cs[i-1]; c[N-i] = 1 - cs[i-1]
        if N % 2 == 0: c[N//2] = sp.Rational(1, 2)
        A = [c[i+1] if i < N else 0 for i in range(N+1)]
        C = [1-c[i-1] if i > 0 else 0 for i in range(N+1)]
        S = N+1; prev, cur = sp.zeros(S), sp.eye(S)
        for m in range(3):
            nxt = sp.zeros(S)
            for i in range(S):
                for j in range(S):
                    e = t*(c[i]-c[m])*cur[i, j] - C[m]*prev[i, j]
                    if i: e += C[i]*cur[i-1, j]
                    if i+1 < S: e += A[i]*cur[i+1, j]
                    nxt[i, j] = e/A[m]
            prev, cur = cur, nxt
        out.append((N, sp.factor(sp.diff(sp.together(cur[N, N]), t).subs(t, 0))))
    return out

# --- first-order tangent cone at Krawtchouk ------------------------------------
def lin_dual(N, w, D=2):
    """t-orders 0..D of all product coefficients for c = K + eps*w, as (value, d/d eps at 0) pairs."""
    S = N+1; c = [F(i, N) for i in range(S)]
    A = [(c[i+1], w[i+1]) if i < N else (F(0), F(0)) for i in range(S)]
    C = [(1-c[i-1], -w[i-1]) if i > 0 else (F(0), F(0)) for i in range(S)]
    zero = [(F(0), F(0))]*(D+1)
    def one():
        z = list(zero); z[0] = (F(1), F(0)); return z
    prev = [[list(zero) for j in range(S)] for i in range(S)]
    cur = [[one() if i == j else list(zero) for j in range(S)] for i in range(S)]
    res = [cur]
    for m in range(S-1):
        am, dam = A[m]; inv = 1/am; dinv = -dam*inv*inv; cm, dcm = C[m]
        nxt = []
        for i in range(S):
            db = (c[i]-c[m], w[i]-w[m]); ai, dai = A[i]; ci, dci = C[i]
            row = []
            for j in range(S):
                e = [[F(0), F(0)] for _ in range(D+1)]
                for l in range(D):
                    v, dv = cur[i][j][l]; e[l+1][0] += db[0]*v; e[l+1][1] += db[0]*dv + db[1]*v
                for l in range(D+1):
                    v, dv = prev[i][j][l]; e[l][0] -= cm*v; e[l][1] -= cm*dv + dcm*v
                    if i:
                        v, dv = cur[i-1][j][l]; e[l][0] += ci*v; e[l][1] += ci*dv + dci*v
                    if i+1 < S:
                        v, dv = cur[i+1][j][l]; e[l][0] += ai*v; e[l][1] += ai*dv + dai*v
                row.append([(v*inv, dv*inv + v*dinv) for v, dv in e])
            nxt.append(row)
        res.append(nxt); prev, cur = cur, nxt
    return res

def drop_direction(N, d):
    """Profile perturbation w (w_0 = w_N = 0, palindromic) whose half-increment drops at nodes 1..h-1 are d."""
    h = (N+1)//2; mult = [2]*h if N % 2 == 0 else [2]*(h-1) + [1]
    dh = [sum(d[s:]) for s in range(h-1)] + [F(0)]
    tot = sum(m*x for m, x in zip(mult, dh)); dh = [x - tot/sum(mult) for x in dh]
    inc = [None]*N
    for i in range(h): inc[i] = dh[i]; inc[N-1-i] = dh[i]
    w = [F(0)]
    for x in inc: w.append(w[-1]+x)
    return w

def tangent_cone(N):
    """Rows G (one per deep point and lowest admissible t-order) with G d >= 0 the necessary first-order
    condition, d = drops at nodes 1..h-1: d/d eps of U_1 at odd deep points with excess >= 3 and of U_2 at
    even deep points with excess >= 4 (where the Krawtchouk value vanishes)."""
    h = (N+1)//2
    Ts = [lin_dual(N, drop_direction(N, [F(int(i == s)) for i in range(h-1)])) for s in range(h-1)]
    rows = []
    for m in range(N+1):
        for i in range(m, N+1):
            for j in range(i, N+1):
                e = m+i+j-2*N; order = 1 if (m+i+j) % 2 else 2
                if not (m+i > N and e >= 3 and order < e): continue
                assert Ts[0][m][i][j][order][0] == 0
                r = [T[m][i][j][order][1] for T in Ts]
                if any(r): rows.append(r)
    return rows

def in_cone(rows, d):
    return all(sum(a*b for a, b in zip(r, d)) >= 0 for r in rows)

def ratio_ranges(rows):
    """LP range of d_s/d_{s+1} over the cone (floating point; rows normalized)."""
    import numpy as np
    from scipy.optimize import linprog
    G = np.array([[float(x) for x in r] for r in rows]); G /= np.abs(G).max(axis=1, keepdims=True)
    D = G.shape[1]; out = []
    for s in range(D-1):
        e = np.eye(D)
        lo = linprog(e[s], A_ub=-G, b_ub=np.zeros(len(G)), A_eq=e[[s+1]], b_eq=[1], bounds=[(None, None)]*D, method='highs')
        hi = linprog(-e[s], A_ub=-G, b_ub=np.zeros(len(G)), A_eq=e[[s+1]], b_eq=[1], bounds=[(None, None)]*D, method='highs')
        out.append((round(lo.fun, 4) if lo.status == 0 else '-inf', round(-hi.fun, 4) if hi.status == 0 else 'inf'))
    return out

def cone_report():
    for N in (8, 10, 12, 14, 16, 20):
        rows = tangent_cone(N); h = (N+1)//2
        k = [F(N, 2) - n for n in range(1, h)]
        flat = [in_cone(rows, [k[s] if s >= j else F(0) for s in range(h-1)]) for j in range(h-1)]
        try:
            rr = ratio_ranges(rows)
        except ImportError:
            rr = 'scipy not available'
        print(f'5. tangent cone N={N}: d_s/d_(s+1) ranges {rr}; rays d_n = (N/2-n) 1[n>j] inside: {flat}', flush=True)

def ratio_hypothesis_counterexample():
    """Drops d_n >= 0 with d_n/(N/2-n) nondecreasing, N = 11: (P) fails at t = 3/25."""
    N, h = 11, 6
    kap = [F(x) for x in (0, 0, 0, 9, 10)]
    d = [kap[s]*(F(N, 2) - (s+1)) for s in range(h-1)]
    half = [1 + sum(d[s:]) for s in range(h-1)] + [F(1)]
    inc = [None]*N
    for i in range(h): inc[i] = half[i]; inc[N-1-i] = half[i]
    c = profile(inc)
    return min_entry(c, [F(3, 25)*x for x in c])

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    for N in (4, 6, 8, 10):
        neg, order = check_krawtchouk(N)
        print(f'1. Krawtchouk N={N}: entries with a negative t-coefficient {neg}; deep entries with other lowest power {order}', flush=True)
    from random import Random
    rng = Random(2)
    for N in (5, 6, 7, 8):
        half = sorted((F(rng.randint(1, 50)) for _ in range((N+1)//2)), reverse=True)
        print(f'2. palindromic B=0, N={N}: (mirror identity, perimeter zeros) = {check_mirror_zero(palindromic(half, N))}', flush=True)
    c = [F(i, 3) for i in range(4)]
    B = [F(0), F(1, 10), F(1, 10), F(1, 10)]
    print(f'3. Krawtchouk off-diagonal N=3, nondecreasing B={[str(x) for x in B]}: min coefficient {min_entry(c, B)}', flush=True)
    try:
        for N, form in first_order_symbolic():
            print(f'4a. B = t c, N={N}: d/dt g(3,N;N) at t=0 = {form}', flush=True)
    except ImportError:
        print('4a. sympy not available; skipping symbolic first-order terms')
    ts = [F(k, 200) for k in range(1, 41)]
    c3 = [F(0), F(1, 4), F(3, 4), F(1)]
    print(f'4b. N=3, c=(0,1/4,3/4,1) (c_1 < 1/3): most negative over t<=1/5: {scan_t(c3, ts)}', flush=True)
    cU = palindromic([F(97), F(87), F(85)], 6)
    print(f'4c. N=6, U-shaped increments (97,87,85,85,87,97): most negative over t<=1/5: {scan_t(cU, ts)}', flush=True)
    cC = palindromic([F(x) for x in (88, 88, 87, 86, 85, 77, 50)], 14)
    v = min_entry(cC, [F(11, 200)*x for x in cC])
    print(f'4d. N=14, concave decreasing half-increments (88,88,87,86,85,77,50), t=11/200: min coefficient {float(v[0]):.4g} at {v[1]}', flush=True)
    cone_report()
    v = ratio_hypothesis_counterexample()
    print(f'6. ratio hypothesis, N=11, increments (19,19,19,19,6,1,...)/169, t=3/25: min coefficient {float(v[0]):.4g} at {v[1]}', flush=True)

if __name__ == '__main__':
    main()
