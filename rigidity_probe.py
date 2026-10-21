"""First-order structure of property (P) at the symmetric Krawtchouk array K(N,1) (Section 8); diagnostics.

Coordinates: stochastic arrays with b_0 = 0 (WLOG by an affine change of x), free coordinates
b_1..b_{N-1}, c_1..c_N (a_n = 1 - b_n - c_n, b_N = 1 - c_N, a_N = 0). A structural zero is a triple
x <= y <= z <= x+y with g(x,y;z) = 0 at K(N,1) (parity and perimeter zeros). Any convex set of arrays
with (P) that contains K(N,1) lies in K(N,1) + T_N, T_N = {v : grad g_p . v >= 0 at every structural zero p}.

Checks:
1. T_N has nonempty interior (no implicit equalities), and an interior direction v gives (P) exactly at
   K(N,1) + eps v (eps = 1e-3, 1e-5): sets with (P) and nonempty interior touch the symmetric endpoint.
2. N-uniform deformation rules delta b_n = beta(n/N), delta c_n = gamma(n/N) with beta, gamma polynomials
   of degree <= d: largest M with an interior rule for all 3 <= N <= M (linear programs; numpy, scipy).
3. Exact certificate that no nonzero constant rule lies in T_3 and T_7.
"""
import argparse
from fractions import Fraction as F
from probe import linearization

def kraw1(N):
    d = [F(i, N) for i in range(N+1)]
    return [1-x for x in d], [F(0)]*(N+1), d[:]

def coords(N):
    return [('b', n) for n in range(1, N)] + [('c', n) for n in range(1, N+1)]

def direction(N, coord):
    da, db, dc = ([F(0)]*(N+1) for _ in range(3))
    kind, n = coord
    if kind == 'b':
        db[n] = F(1); da[n] = F(-1)
    else:
        dc[n] = F(1)
        if n < N: da[n] = F(-1)
        else: db[N] = F(-1)
    return da, db, dc

def lin_dual(a, b, c, da, db, dc):
    """Product coefficients with their directional derivatives, entries (value, derivative)."""
    S = len(a)
    prev = [[(F(0), F(0)) for j in range(S)] for i in range(S)]
    cur = [[(F(int(i == j)), F(0)) for j in range(S)] for i in range(S)]
    res = [cur]
    for m in range(S-1):
        inv = 1/a[m]; dinv = -da[m]*inv*inv
        nxt = []
        for i in range(S):
            row = []
            for j in range(S):
                v = (b[i]-b[m])*cur[i][j][0] - c[m]*prev[i][j][0]
                dv = ((b[i]-b[m])*cur[i][j][1] + (db[i]-db[m])*cur[i][j][0]
                      - c[m]*prev[i][j][1] - dc[m]*prev[i][j][0])
                if i:
                    v += c[i]*cur[i-1][j][0]; dv += c[i]*cur[i-1][j][1] + dc[i]*cur[i-1][j][0]
                if i+1 < S:
                    v += a[i]*cur[i+1][j][0]; dv += a[i]*cur[i+1][j][1] + da[i]*cur[i+1][j][0]
                row.append((v*inv, dv*inv + v*dinv))
            nxt.append(row)
        res.append(nxt); prev, cur = cur, nxt
    return res

def zero_gradients(N):
    a, b, c = kraw1(N)
    C = coords(N)
    Ts = [lin_dual(a, b, c, *direction(N, co)) for co in C]
    Z = [((x, y, z), [T[x][y][z][1] for T in Ts]) for x in range(N+1) for y in range(x, N+1)
         for z in range(y, min(x+y, N)+1) if Ts[0][x][y][z][0] == 0]
    return C, Z

def interior_check(N):
    import numpy as np
    from scipy.optimize import linprog
    C, Z = zero_gradients(N)
    G = np.array([[float(x) for x in g] for _, g in Z]); Gn = G/np.abs(G).max(axis=1, keepdims=True)
    m, n = Gn.shape
    res = linprog(np.concatenate([np.zeros(n), [-1.]]), A_ub=np.hstack([-Gn, np.ones((m, 1))]), b_ub=np.zeros(m),
                  bounds=[(-1, 1)]*n + [(None, None)], method='highs')
    v = [F(x).limit_denominator(1000) for x in res.x[:n]]
    slack = min(sum(gi*vi for gi, vi in zip(g, v)) for _, g in Z)
    a, b, c = kraw1(N)
    ok = []
    for eps in (F(1, 10**3), F(1, 10**5)):
        A, B, Cc = list(a), list(b), list(c)
        for co, vi in zip(C, v):
            for arr, dv in zip((A, B, Cc), direction(N, co)):
                for i in range(N+1): arr[i] += eps*vi*dv[i]
        g = linearization(A, B, Cc)
        ok.append(all(x >= 0 for G_ in g for row in G_ for x in row))
    return res.x[-1], slack, ok

def uniform_rules(degrees, top=18):
    import numpy as np
    from scipy.optimize import linprog
    from numpy.polynomial import chebyshev as Ch
    cache = {N: zero_gradients(N) for N in range(3, top+1)}
    def rows(N, deg):
        C, Z = cache[N]
        B = np.zeros((len(C), 2*(deg+1)))
        for idx, (kind, n) in enumerate(C):
            for k in range(deg+1):
                e = np.zeros(deg+1); e[k] = 1
                B[idx, k if kind == 'b' else deg+1+k] = Ch.chebval(2*n/N - 1, e)
        R = np.array([[float(v) for v in g] for _, g in Z]) @ B
        nr = np.abs(R).max(axis=1); keep = nr > 1e-12
        return R[keep]/nr[keep, None]
    out = {}
    for deg in degrees:
        best = None
        for M in range(4, top+1):
            R = np.vstack([rows(N, deg) for N in range(3, M+1)]); k = R.shape[1]
            res = linprog(np.concatenate([np.zeros(k), [-1.]]), A_ub=np.hstack([-R, np.ones((len(R), 1))]),
                          b_ub=np.zeros(len(R)), bounds=[(-1, 1)]*k + [(None, 1)], method='highs')
            if res.x[-1] > 1e-7: best = (M, res.x[-1])
            else: break
        out[deg] = best
    return out

def constant_rule_certificate():
    """Slacks of the constant rule (beta0, gamma0) at three structural zeros, and exact positive weights
    whose combination vanishes identically: hence beta0 = gamma0 = 0 for any constant rule in T_3 and T_7."""
    def row(N, p):
        C, Z = zero_gradients(N); g = dict(Z)[p]
        return [sum(gi for gi, (k, _) in zip(g, C) if k == 'b'), sum(gi for gi, (k, _) in zip(g, C) if k == 'c')]
    rows = [row(3, (3, 3, 3)), row(7, (4, 6, 6)), row(7, (6, 6, 6))]
    w = [F(247, 960), F(41, 64), F(1)]
    combo = [sum(wi*r[j] for wi, r in zip(w, rows)) for j in range(2)]
    return rows, w, combo

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    rows, w, combo = constant_rule_certificate()
    print(f'3. constant rule: slack rows {[[str(x) for x in r] for r in rows]}, weights {[str(x) for x in w]}, '
          f'combination {[str(x) for x in combo]}', flush=True)
    try:
        import scipy  # noqa: F401
    except ImportError:
        print('scipy not available; skipping linear programs'); return
    for N in (4, 6, 8, 10):
        margin, slack, ok = interior_check(N)
        print(f'1. N={N}: LP margin {margin:.3g}; exact minimum first-order slack {float(slack):.3g}; '
              f'(P) at K(N,1)+eps v for eps=1e-3, 1e-5: {ok}', flush=True)
    for deg, best in uniform_rules((1, 3, 5, 7, 9, 11, 13)).items():
        print(f'2. degree {deg}: interior rule for all 3 <= N <= {best[0] if best else "-"}'
              + (f' (margin {best[1]:.3g})' if best else ''), flush=True)

if __name__ == '__main__':
    main()
