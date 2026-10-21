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
4. Corner identity (proved in RESEARCH.md for every N; checked here exactly for N <= 20): the derivative of
   g(N,N;N) at K(N,1) is s_N * sum_{n=0}^N (-1)^n C(N,n) F_N(n), with F_N = db + 2 dc (N even), db (N odd),
   db_0 = dc_0 = 0, db_N = -dc_N, and s_N = (-1)^(floor(N/2)+1) / C(N-1, floor((N-1)/2)).
5. Consequence for polynomial uniform rules (degree < N): the derivative is -s_N L_even (N even) or
   -s_N L_odd (N odd), L_even = beta(0)+2gamma(0)+beta(1)+gamma(1), L_odd = beta(0)-beta(1)-gamma(1);
   s_N changes sign from N to N+2, so L != 0 breaks (P) near K(N,1) for infinitely many N (checked exactly).
6. Boundary layers: with c_N changed separately by L (possible when L_even = L_odd), the corner slack vanishes.
7. r < 1: g(N,N;N) = (1-r)^N at K(N,r); a fixed-size rule fails at fixed r in (1/2, 1) for many N
   (r = 4/5, eps = 1/100; r = 19/20, eps = 1/1000) but not at r = 1/2 for N <= 14.
9. Below r = 1/2, small N only (N <= 26): additive rules at fixed size, valid only while N < 1/eps; these
   checks are superseded by smallr_probe.py, which tests valid deformations at N ~ 5/r^2.
8. Noerlund-Rice region (mpmath): D_N[f] = sum (-1)^n C(N,n) f(n/N) decays when the poles of f lie outside
   the football Omega = {U <= -1}, U(x) = int_0^1 log|x-t| dt, and grows when they lie inside.
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

def s_N(N):
    from math import comb
    return F((-1)**(N//2 + 1), comb(N-1, (N-1)//2))

def corner_identity(N):
    """Exact gradient of g(N,N;N) at K(N,1) equals the alternating binomial stencil."""
    from math import comb
    C, Z = zero_gradients(N)
    g = dict(Z)[(N, N, N)]
    want = []
    for kind, n in C:
        if kind == 'b': want.append(s_N(N)*(-1)**n*comb(N, n))
        elif n < N: want.append(2*s_N(N)*(-1)**n*comb(N, n) if N % 2 == 0 else F(0))
        else: want.append(s_N(N))
    return list(g) == want

def uniform_rule_signs(beta, gamma, Ns, eps=F(1, 10**6)):
    """Sign of g(N,N;N) at K(N,1) + eps*v_N for the rule (beta, gamma), and whether (P) holds there."""
    out = []
    for N in Ns:
        a, b, c = kraw1(N)
        A, B, Cc = list(a), list(b), list(c)
        for n in range(1, N):
            B[n] += eps*beta(F(n, N)); A[n] -= eps*beta(F(n, N))
        for n in range(1, N+1):
            Cc[n] += eps*gamma(F(n, N))
            if n < N: A[n] -= eps*gamma(F(n, N))
            else: B[N] -= eps*gamma(F(n, N))
        g = linearization(A, B, Cc)
        out.append((N, (g[N][N][N] > 0) - (g[N][N][N] < 0), all(x >= 0 for G in g for row in G for x in row)))
    return out

def krawr(N, r):
    d = [F(i, N) for i in range(N+1)]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def rule_at(N, r, beta, gamma, eps):
    a, b, c = krawr(N, r); A, B, Cc = list(a), list(b), list(c)
    for n in range(1, N):
        B[n] += eps*beta(F(n, N)); A[n] -= eps*beta(F(n, N))
    for n in range(1, N+1):
        Cc[n] += eps*gamma(F(n, N))
        if n < N: A[n] -= eps*gamma(F(n, N))
        else: B[N] -= eps*gamma(F(n, N))
    return A, B, Cc

def fixed_r_report():
    ok = all(linearization(*krawr(N, r))[N][N][N] == (1-r)**N for N in range(1, 11) for r in (F(1, 3), F(1, 2), F(9, 10)))
    print(f'7. g(N,N;N) = (1-r)^N at K(N,r) for N <= 10, r in {{1/3, 1/2, 9/10}}: {ok}', flush=True)
    for r, eps in ((F(19, 20), F(1, 1000)), (F(4, 5), F(1, 100)), (F(1, 2), F(1, 100))):
        res = []
        for N in range(4, 15):
            g = linearization(*rule_at(N, r, lambda x: F(1), lambda x: F(0), eps))
            P = all(x >= 0 for G in g for row in G for x in row)
            res.append(f'{N}:' + ('ok' if P else ('corner<0' if g[N][N][N] < 0 else 'noP')))
        print(f'7. r={r}, rule beta=1, gamma=0, eps={eps}: ' + ' '.join(res), flush=True)

def layer_report():
    for N in range(4, 13):
        C, Z = zero_gradients(N); g = dict(Z)[(N, N, N)]
        with_layer = [F(1) if k == 'b' else (F(-1, 2) if n < N else F(0)) for k, n in C]
        without = [F(1) if k == 'b' else F(-1, 2) for k, n in C]
        a = sum(x*y for x, y in zip(g, with_layer)); b = sum(x*y for x, y in zip(g, without))
        assert a == 0 and b == -s_N(N)/2
    print('6. bulk rule beta=1, gamma=-1/2 (L_even = L_odd = 1/2): corner slack -s_N/2 without layer, 0 with dc_N layer, N = 4..12', flush=True)

def football_report():
    try:
        import mpmath as mp
    except ImportError:
        print('8. mpmath not available; skipping'); return
    mp.mp.dps = 120
    def U(z):
        f = lambda w: w*mp.log(w) if w != 0 else mp.mpf(0)
        return mp.re(f(z) - f(z-1)) - 1
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(100):
        mid = (lo+hi)/2
        if U(mp.mpc(0.5, mid)) < -1: lo = mid
        else: hi = mid
    print(f'8. football Omega crosses Re x = 1/2 at Im x = +-{float(lo):.4f}', flush=True)
    for y in (0.2, 0.25, 0.28, 0.35):
        f = lambda x, y=y: 1/((x-mp.mpf(0.5))**2 + mp.mpf(y)**2)
        vals = [mp.fsum(((-1)**n)*mp.binomial(N, n)*f(mp.mpf(n)/N) for n in range(N+1)) for N in (20, 40, 80, 120)]
        print(f'8. f = 1/((x-1/2)^2+{y}^2) ({"inside" if U(mp.mpc(0.5, y)) < -1 else "outside"} Omega): '
              f'|D_N| for N = 20, 40, 80, 120: ' + ' '.join(f'{float(abs(v)):.1e}' for v in vals), flush=True)

def below_half_report():
    rules = (('beta=1', lambda x: F(1), lambda x: F(0)), ('gamma=x', lambda x: F(0), lambda x: x))
    for r in (F(1, 5), F(1, 3), F(2, 5)):
        ok = all(all(x >= 0 for G in linearization(*rule_at(N, r, be, ga, sg*F(1, 100))) for row in G for x in row)
                 for _, be, ga in rules for sg in (1, -1) for N in range(4, 17, 2))
        print(f'9. r={r}: rules beta=+-1, gamma=+-x at eps=1/100 keep (P) for even N <= 16: {ok}', flush=True)
    kinks = (('beta=|x-2/5|', lambda x: abs(x - F(2, 5)), lambda x: F(0)),
             ('gamma=(x-3/5)_+', lambda x: F(0), lambda x: max(F(0), x - F(3, 5))),
             ('gamma=-(x-3/5)_+', lambda x: F(0), lambda x: -max(F(0), x - F(3, 5))))
    for r in (F(1, 5), F(2, 5)):
        for name, be, ga in kinks:
            first = next((N for N in range(8, 27, 3)
                          if not all(x >= 0 for G in linearization(*rule_at(N, r, be, ga, F(1, 20))) for row in G for x in row)), None)
            print(f'9. r={r} kinked rule {name}, eps=1/20: first failing N in 8, 11, ..., 26: {first}', flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    print('4. corner identity exact for N = 2..20:', all(corner_identity(N) for N in range(2, 21)), flush=True)
    for name, be, ga in (('beta=1, gamma=0 (L_even=2, L_odd=0)', lambda x: F(1), lambda x: F(0)),
                         ('beta=0, gamma=x (L_even=1, L_odd=-1)', lambda x: F(0), lambda x: x),
                         ('beta=x, gamma=-x (Krawtchouk direction, L=0)', lambda x: x, lambda x: -x)):
        res = uniform_rule_signs(be, ga, range(4, 15))
        print(f'5. {name}: sign of g(N,N;N), (P): ' + ' '.join(f'N={N}:{ {1: "+", -1: "-", 0: "0"}[sg] }{"" if P else "/noP"}' for N, sg, P in res), flush=True)
    layer_report()
    fixed_r_report()
    football_report()
    below_half_report()
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
