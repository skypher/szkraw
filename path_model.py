"""Signed path models for deep product coefficients (Section 8); diagnostics, not a proof.

1. Viennot expansion. With P_n = a_0...a_{n-1} R_n (monic: xP_n = P_{n+1} + b_n P_n + lam_n P_{n-1},
   lam_n = a_{n-1} c_n), the coefficient a_0...a_{n-1} g(n,m;k) equals P_n(J)[m][k], a signed sum over
   monomer-dimer tilings of {0..n-1} and lattice paths m -> k with one step per monomer i (up a_h,
   down c_h, level b_h - b_i) and weight -lam_i per dimer {i-1,i}. We report the positive and negative
   mass of this sum and the cancellation factor (positive mass)/(net value).
2. Szwarc lightcone expansion. In Szwarc's normalization (3.9) with sigma_n = r^(n/2), the checkerboard
   cone v of the apex (n,m), truncated at the ceiling, gives alpha_m u(n,m) = sum_p (H*v)(p) u(p).
   Below the ceiling every weight is nonnegative under Theorem 7.10's hypotheses; we report where
   negative weights occur for deep apexes and their share of the total.
3. Mirror pairing. M(x,y) = (N-y,N-x). For arrays with lambda_i = lambda_{N+1-i}, in a normalization with
   A_{N-i} = C_i, the defects pair exactly with their mirrors, and w = u - u o M satisfies
   Hw = -(e_x - e_y) u o M with e_i = b_i - b_{N-i}. We test w >= 0 for x+y > N ("mirror dominance")
   and search for maximum-principle certificates for w (linear programs; need numpy and scipy).
"""
import argparse
from fractions import Fraction as F
from probe import linearization
from deep_certificates import hstar, deep_points
from szwarc_check import geometric

def viennot_masses(a, b, c, n, m, k):
    """Positive and negative mass of the Viennot expansion of P_n(J)[m][k]."""
    N = len(a)-1
    lam = [F(0)] + [a[i-1]*c[i] for i in range(1, N+1)]
    # state after processing labels < i: dict height -> (pos, neg); two layers for dimers
    def step(layer, i):
        out = {}
        def add(h, w, pn):
            p, q = out.get(h, (F(0), F(0)))
            if w >= 0: out[h] = (p + w*pn[0], q + w*pn[1])
            else: out[h] = (p - w*pn[1], q - w*pn[0])
        for h, pn in layer.items():
            if h < N and a[h]: add(h+1, a[h], pn)
            if h > 0: add(h-1, c[h], pn)
            if b[h] != b[i]: add(h, b[h]-b[i], pn)
        return out
    def merge(x, y):
        z = dict(x)
        for h, (p, q) in y.items():
            p0, q0 = z.get(h, (F(0), F(0))); z[h] = (p0+p, q0+q)
        return z
    layers = {-1: {}, 0: {m: (F(1), F(0))}}   # layers[i] = state after labels 0..i-1
    for i in range(n):
        mono = step(layers[i], i)
        if i >= 1:   # dimer {i-1, i}: weight -lam_i applied to state after labels < i-1
            dim = {h: (lam[i]*q, lam[i]*p) for h, (p, q) in layers[i-1].items()}
            mono = merge(mono, dim)
        layers[i+1] = mono
    p, q = layers[n].get(k, (F(0), F(0)))
    return p, q

def szwarc_arrays(a, b, c, sigma):
    """Array (A,B,C) of the P~ normalization: x P~_i = A_i P~_{i+1} + B_i P~_i + C_i P~_{i-1}."""
    N = len(a)-1
    gam = [a[i]*sigma[i+1]/sigma[i] if i < N else F(0) for i in range(N+1)]
    alp = [c[i]*sigma[i-1]/sigma[i] if i > 0 else F(0) for i in range(N+1)]
    A = [alp[i+1] if i < N else F(0) for i in range(N+1)]
    C = [gam[i-1] if i > 0 else F(0) for i in range(N+1)]
    return A, list(b), C, alp, gam

def lightcone(A, B, C, n, m):
    """H*v for Szwarc's checkerboard cone of apex (n,m), truncated to the grid."""
    N = len(A)-1
    v = {(i, j): F(1) for j in range(m) for i in range(N+1) if abs(i-n) < m-j and (n+m-i-j) % 2 == 1}
    return hstar(A, B, C, v)

def run(N, s):
    """Krawtchouk at r = s^2, so that Szwarc's sigma_n = r^(n/2) = s^n is rational."""
    r = s*s
    a, b, c = geometric(N, F(1), r)
    g = linearization(a, b, c)
    fac_deep, fac_low = [], []
    for k in range(N+1):
        for m in range(N+1):
            for n in range(1, N+1):
                x = g[n][m][k]
                if x <= 0: continue
                p, q = viennot_masses(a, b, c, n, m, k)
                prod = F(1)
                for i in range(n): prod *= a[i]
                assert p - q == prod*x
                (fac_deep if (n+m > N and n+k > N and m+k > N) else fac_low).append(float(p/(p-q)))
    A, B, C, alp, gam = szwarc_arrays(a, b, c, [s**i for i in range(N+1)])
    u = linearization(A, B, C)
    stats = []
    for n, m, k in deep_points(N):
        w = lightcone(A, B, C, n, m)
        assert w.get((n, m), 0) == -A[m-1]
        assert sum(wt*u[x][y][k] for (x, y), wt in w.items()) == 0
        negs = {p: wt for p, wt in w.items() if wt < 0 and p != (n, m)}
        pos = sum(wt*u[x][y][k] for (x, y), wt in w.items() if wt > 0)
        neg = sum(-wt*u[x][y][k] for (x, y), wt in negs.items())
        stats.append((n, m, k, negs, all(x == N for x, y in negs), float(neg/pos) if pos else None))
    return fac_low, fac_deep, stats

def palindromic_sample(trials=400, seed=11):
    """Random palindromic-lambda perturbations of Krawtchouk with e nondecreasing and nonnegative low
    products: counts of ((P), mirror dominance)."""
    from random import Random
    rng = Random(seed); out = {}
    for _ in range(trials):
        N = rng.choice([4, 5, 6, 7]); r = F(rng.randint(1, 9), 10)
        bmid = [max(F(0), (1-r)*F(i, N) + F(rng.randint(-3, 3), 100)) for i in range(1, N)]
        lam_half = [r*F(i*(N-i+1), N*N)*(1 + F(rng.randint(-10, 10), 100)) for i in range(1, (N+1)//2 + 1)]
        arr = lambda_palindromic(N, bmid, lam_half)
        if arr is None: continue
        a, b, c = arr
        e = [b[i]-b[N-i] for i in range(N+1)]
        if not all(e[i] <= e[i+1] for i in range(N)): continue
        g = linearization(a, b, c)
        if not all(g[x][y][k] >= 0 for x in range(N+1) for y in range(N+1) for k in range(N+1)
                   if min(x+y, x+k, y+k) <= N): continue
        P = all(x >= 0 for G in g for row in G for x in row)
        A, B, C, _, _ = szwarc_arrays(a, b, c, self_mirror_sigma(a, b, c))
        u = linearization(A, B, C); tol = F(1, 10**25)
        MD = all(u[x][y][k] - u[N-y][N-x][k] >= -tol for k in range(N+1) for x in range(N+1)
                 for y in range(N+1) if x+y > N)
        out[(P, MD)] = out.get((P, MD), 0) + 1
    return out

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--sizes', type=int, nargs='+', default=[4, 6])
    args = parser.parse_args()
    for N in args.sizes:
        for sq in (F(1, 5), F(1, 2), F(9, 10)):
            r = sq*sq
            low, deep, stats = run(N, sq)
            with_neg = [s for s in stats if s[3]]
            side = all(x-y == n-m and x+y >= N-1 for n, m, k, negs, _, _ in with_neg for (x, y) in negs)
            print(f'N={N} r={r}: Viennot cancellation factor non-deep max {max(low):.3g}, deep max {max(deep):.3g}; '
                  f'lightcone negative weights at {len(with_neg)}/{len(stats)} deep apexes, '
                  f'all on the side edge x-y=n-m with x+y>=N-1: {side}', flush=True)
    for N in (4, 6, 8):
        viol = sum(len(run_mirror(N, sq)) for sq in (F(1, 5), F(1, 2), F(9, 10), F(99, 100)))
        print(f'mirror dominance, Krawtchouk N={N}, r in {{1/25,1/4,81/100,9801/10000}}: {viol} violations', flush=True)
    print('palindromic-lambda sample, counts of ((P), mirror dominance):', palindromic_sample(), flush=True)
    try:
        import scipy  # noqa: F401
    except ImportError:
        print('scipy not available; skipping mirror certificate LPs'); return
    for N in (4, 6, 8):
        for ts in ([F(4)], [F(1, 2)], [F(1, 2), F(4)]):
            arrs = [kraw_szwarc(N, t) for t in ts]
            fail = [q for q in high_points(N) if not mirror_certify(arrs, *q, 0, order='y')]
            print(f'mirror certificates N={N} t={[str(t) for t in ts]}: {len(high_points(N))-len(fail)}/{len(high_points(N))} '
                  f'high apexes; failing {fail}', flush=True)


# --- mirror dominance -------------------------------------------------------
def mirror_defects(a, b, c, s):
    """Points (x,y,k) with x+y > N and u(x,y) < u(N-y,N-x) in Szwarc's normalization sigma_n = s^n."""
    N = len(a)-1
    A, B, C, _, _ = szwarc_arrays(a, b, c, [s**i for i in range(N+1)])
    u = linearization(A, B, C)
    bad = [(x, y, k, u[x][y][k], u[N-y][N-x][k]) for k in range(N+1) for x in range(N+1)
           for y in range(N+1) if x+y > N and u[x][y][k] < u[N-y][N-x][k]]
    return bad, u

def run_mirror(N, s):
    a, b, c = geometric(N, F(1), s*s)
    bad, u = mirror_defects(a, b, c, s)
    return bad

# --- certificates for w = u - u o M ----------------------------------------
def canon(N, p):
    """Canonical representative of p under swap and the mirror M(x,y) = (N-y,N-x); w(p) = sign*w(rep)."""
    x, y = max(p), min(p)
    if x + y > N: return (x, y), 1
    if x + y == N: return None, 0
    return (N-y, N-x), -1

def mirror_certify(arrays, n, m, k, order='sum', support=None, oneshot=False):
    """Search v with sum_q coef(q) w(q) = -sum_p v(p)(e_x-e_y) u(M p), where coef is H*v folded by swap
    and mirror, coef(apex) = -1, coef >= 0 at points known by induction, 0 at unknown points, and
    v(p)(e_x - e_y) >= 0 wherever v is allowed. One v must serve every array in `arrays`."""
    import numpy as np
    from scipy.optimize import linprog
    N = len(arrays[0][0])-1
    pts = support if support is not None else [(i, j) for i in range(N+1) for j in range(N+1)]
    key = {'sum': lambda q: (q[0]+q[1], q[0]-q[1]), 'sumdesc': lambda q: (q[0]+q[1], q[1]-q[0]),
           'y': lambda q: (q[1], q[0]), 'diff': lambda q: (q[0]-q[1], q[0]+q[1]), 'x': lambda q: (-q[0], q[1])}[order]
    apex = (n, m)
    Aeq, beq, Aub = [], [], []
    for A, B, C in arrays:
        e = [B[i]-B[N-i] for i in range(N+1)]
        rows = {}
        for idx, p in enumerate(pts):
            i, j = p
            def add(q, wt):
                rep, sg = canon(N, q)
                if rep is None or wt == 0: return
                rows.setdefault(rep, np.zeros(len(pts)))[idx] += sg*float(wt)
            if i < N: add((i+1, j), A[i])
            if i > 0: add((i-1, j), C[i])
            add((i, j), B[i]-B[j])
            if j < N: add((i, j+1), -A[j])
            if j > 0: add((i, j-1), -C[j])
        for q, row in rows.items():
            if q == apex: Aeq.append(row); beq.append(-1.)
            elif not oneshot and key(q) < key(apex): Aub.append(-row)
            else: Aeq.append(row); beq.append(0.)
        # source sign: v(p)(e_x - e_y) >= 0
        for idx, (i, j) in enumerate(pts):
            if e[i] == e[j]: continue
            row = np.zeros(len(pts)); row[idx] = -float(e[i]-e[j])
            if i + j >= N: Aub.append(row)       # u(M p) is a non-deep coefficient, >= 0 by Theorem 7.10
            else:                                # u(M p) >= 0 only once w(M p) is known
                rep, _ = canon(N, (N-j, N-i))
                if rep is not None and not oneshot and key(rep) < key(apex): Aub.append(row)
                else:
                    row[idx] = 1.; Aeq.append(row); beq.append(0.)
    res = linprog(np.zeros(len(pts)), A_ub=np.array(Aub) if Aub else None, b_ub=[0.]*len(Aub) or None,
                  A_eq=np.array(Aeq), b_eq=beq, bounds=[(None, None)]*len(pts), method='highs')
    return res.status == 0

def kraw_szwarc(N, t):
    """Krawtchouk in Szwarc's normalization divided by s: A_i = d_{i+1}, C_i = 1-d_{i-1}, B = t d, t = 1/s - s."""
    d = [F(i, N) for i in range(N+1)]
    A = [d[i+1] if i < N else F(0) for i in range(N+1)]
    C = [1-d[i-1] if i > 0 else F(0) for i in range(N+1)]
    return A, [t*x for x in d], C

def high_points(N):
    return [(x, y) for x in range(N+1) for y in range(x+1) if x+y > N]

# --- palindromic-lambda arrays -------------------------------------------------
def lambda_palindromic(N, bmid, lam_half):
    """Array with b_0 = 0, given b_1..b_{N-1}, lambda_i = a_{i-1} c_i palindromic (first half given);
    b_N is solved from the terminal row sum. Returns None if a coordinate leaves its range."""
    lam = [F(0)]*(N+1)
    for i in range(1, N+1):
        lam[i] = lam_half[min(i, N+1-i)-1]
    b = [F(0)] + list(bmid) + [F(0)]
    a = [F(1)] + [F(0)]*N; c = [F(0)]*(N+1)
    for i in range(1, N+1):
        c[i] = lam[i]/a[i-1]
        if i < N:
            a[i] = 1 - b[i] - c[i]
            if a[i] <= 0 or c[i] <= 0: return None
    b[N] = 1 - c[N]
    if b[N] < 0 or c[N] <= 0: return None
    return a, b, c

def self_mirror_sigma(a, b, c, digits=40):
    """sigma with A_{N-i} = C_i, symmetric choice rho_i = rho_{N+1-i} = sqrt(c_{N+1-i}/a_{i-1}),
    square roots rounded to `digits` decimals (diagnostic precision)."""
    from decimal import Decimal, getcontext
    getcontext().prec = digits + 10
    N = len(a)-1
    sig = [F(1)]
    for i in range(1, N+1):
        q = c[N+1-i]/a[i-1]
        root = (Decimal(q.numerator)/Decimal(q.denominator)).sqrt()
        sig.append(sig[-1]*F(root).limit_denominator(10**digits))
    return sig

if __name__ == '__main__':
    main()
