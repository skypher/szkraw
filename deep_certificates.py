"""Diagnostics for the open deep-triple problem (Section 8); negative results, not a proof.

Exact parts use Fractions only. The lightcone certificate searches are linear programs
solved in floating point and need numpy and scipy; they are skipped if those are missing.
Not called from verify.py.

Notation. Fix k and put u(x,y) = g(x,y;k). Then Hu = 0 on {0..N}^2, where
(Hu)(i,j) = a_i u(i+1,j) + b_i u(i,j) + c_i u(i-1,j) - a_j u(i,j+1) - b_j u(i,j) - c_j u(i,j-1).
A certificate for the deep point (n,m), n >= m, is a weight v with <Hu,v> = 0, so that
u(n,m) = sum of (H*v)(p) u(p) over the other points p. It proves u(n,m) >= 0 when
(H*v)(p) >= 0 wherever u(p) is already known to be nonnegative and (H*v)(p) = 0 elsewhere.
"""
import argparse
import itertools
from fractions import Fraction as F
from probe import linearization
from szwarc_check import geometric, reversed_array

def is_deep(N, x, y, k):
    return x+y > N and x+k > N and y+k > N

def deep_points(N):
    return [(n, m, k) for k in range(N+1) for m in range(N+1) for n in range(m, N+1) if is_deep(N, n, m, k)]

def profile(inc, r):
    d = [F(0)]
    for x in inc: d.append(d[-1]+x)
    d = [x/d[-1] for x in d]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def hstar(a, b, c, v):
    """H*v, symmetrised through u(x,y) = u(y,x); keys (x,y) with x >= y."""
    N = len(a)-1; out = {}
    def add(p, w):
        q = (max(p), min(p)); out[q] = out.get(q, 0) + w
    for (i, j), val in v.items():
        if i < N: add((i+1, j), a[i]*val)
        if i > 0: add((i-1, j), c[i]*val)
        add((i, j), (b[i]-b[j])*val)
        if j < N: add((i, j+1), -a[j]*val)
        if j > 0: add((i, j-1), -c[j]*val)
    return out

# --- exact checks -----------------------------------------------------------
def tilted_reversal(N, r):
    """W[t][z] = g(N,N-t;z) is triangular with positive diagonal, so T = W always 'works'."""
    a, b, c = geometric(N, F(1), r); g = linearization(a, b, c)
    W = [[g[N][N-t][z] for z in range(N+1)] for t in range(N+1)]
    assert all(W[t][z] == 0 for t in range(N+1) for z in range(t)) and all(W[t][t] > 0 for t in range(N+1))
    # explicit reference T = W of symmetric Krawtchouk: the reversed factor U T goes negative
    g1 = linearization(*geometric(N, F(1), F(1))); gp = linearization(*reversed_array(a, b, c))
    UT = min(sum(gp[N-x][N-y][t]*g1[N][N-t][z] for t in range(N+1))
             for x in range(N+1) for y in range(N+1) if x+y > N for z in range(N+1))
    return UT

def site_dependent_values(rs):
    """Number of distinct values of sum y_j with y_j in {1, -r_j}."""
    return len({sum((F(1) if s else -r) for s, r in zip(S, rs)) for S in itertools.product([0, 1], repeat=len(rs))})

def bias_scan():
    """The N = 14 convex counterexample profile across r: (P) fails only on an interior r-window."""
    inc = [F(1)]*7 + [F(6, 5)]*7
    out = []
    for r in [F(1, 100), F(1, 5), F(2, 5), F(1, 2), F(7, 10), F(1)]:
        g = linearization(*profile(inc, r))
        out.append((r, sum(1 for G in g for row in G for x in row if x < 0)))
    return out

def marching(a, b, c, n, m, k):
    """Canonical Riemann function: H*v = 0 at every deep point except the apex, marching down in j."""
    N = len(a)-1; v = {}
    V = lambda x, y: v.get((x, y), F(0))
    for y in range(m, 0, -1):
        for x in range(N+1):
            if abs(x-n) > m-y or not is_deep(N, x, y, k): continue
            rhs = ((a[x-1]*V(x-1, y) if x > 0 else 0) + (c[x+1]*V(x+1, y) if x < N else 0)
                   + (b[x]-b[y])*V(x, y) - (c[y+1]*V(x, y+1) if y < N else 0))
            if (x, y) == (n, m): rhs += 1
            v[(x, y-1)] = rhs/a[y-1]
    hs = hstar(a, b, c, v)
    assert hs[(n, m)] == -1 and all(w == 0 for p, w in hs.items() if p != (n, m) and is_deep(N, *p, k))
    return {p: w for p, w in hs.items() if w != 0 and not is_deep(N, *p, k)}

def run_marching(N, r):
    a, b, c = geometric(N, F(1), r); g = linearization(a, b, c)
    good, worst = 0, None
    for n, m, k in deep_points(N):
        flux = marching(a, b, c, n, m, k)
        assert sum(w*g[x][y][k] for (x, y), w in flux.items()) == g[n][m][k]
        if all(w >= 0 for w in flux.values()): good += 1
        elif (n, m, k) == (N, N, 1): worst = min(flux.values())
    return good, len(deep_points(N)), worst

# --- linear programs --------------------------------------------------------
def certify(arr, n, m, k, support='free', known='induction', vpos=False):
    """Search for a certificate for u(n,m) on the backward cone {j < m, |i-n| < m-j}.
    support: 'free' (any weight), 'parity' (Szwarc's checkerboard), or 'phi_s', 'phi_s_par',
    'psi_d_par', 'phi_i_par', 'phi_j_par' (one free weight per value of i+j, i-j, i or j).
    known: 'induction' (non-deep points and all points with second coordinate < m)
    or 'oneshot' (non-deep points only)."""
    import numpy as np
    from scipy.optimize import linprog
    arrays = arr if isinstance(arr, list) else [arr]
    N = len(arrays[0][0])-1
    pts = [(i, j) for j in range(m) for i in range(N+1) if abs(i-n) < m-j]
    par = [p for p in pts if (n+m-p[0]-p[1]) % 2 == 1]
    keyfn = {'free': (lambda i, j: (i, j), pts), 'parity': (lambda i, j: (i, j), par),
             'phi_s': (lambda i, j: i+j, pts), 'phi_s_par': (lambda i, j: i+j, par),
             'psi_d_par': (lambda i, j: i-j, par), 'phi_i_par': (lambda i, j: i, par),
             'phi_j_par': (lambda i, j: j, par)}[support]
    key, P = keyfn
    keys = sorted({key(*p) for p in P}, key=str)
    basis = [{p: 1. for p in P if key(*p) == kk} for kk in keys]
    Aeq, beq, Aub = [], [], []
    for a, b, c in arrays:    # one weight for all arrays: H*v is linear in the coefficients
        a, b, c = ([float(x) for x in y] for y in (a, b, c))
        cols = [hstar(a, b, c, B) for B in basis]
        for p in sorted(set().union(*cols)):
            row = np.array([col.get(p, 0.) for col in cols]); x, y = p
            ok = not is_deep(N, x, y, k) or (known == 'induction' and y < m)
            if p == (n, m): Aeq.append(row); beq.append(-1.)
            elif ok: Aub.append(-row)
            else: Aeq.append(row); beq.append(0.)
    res = linprog(np.zeros(len(basis)), A_ub=np.array(Aub) if Aub else None, b_ub=[0.]*len(Aub) or None,
                  A_eq=np.array(Aeq), b_eq=beq, bounds=[(0 if vpos else None, None)]*len(basis), method='highs')
    return res.status == 0

def count(arr, N, **kw):
    return sum(certify(arr, *t, **kw) for t in deep_points(N)), len(deep_points(N))

def run_lp(N):
    K = lambda r: geometric(N, F(1), r)
    for r in [F(1), F(1, 2), F(1, 5)]:
        print(f'  N={N} r={r}: free {count(K(r), N)}, one-shot {count(K(r), N, known="oneshot")}, '
              f'parity {count(K(r), N, support="parity")}, v>=0 {count(K(r), N, vpos=True)}', flush=True)
    for s in ['phi_s', 'phi_s_par', 'psi_d_par', 'phi_i_par', 'phi_j_par']:
        print(f'  N={N} r=1/5 {s}: {count(K(F(1, 5)), N, support=s)}', flush=True)
    print(f'  N={N} parity at r=99/100: {count(K(F(99, 100)), N, support="parity")}', flush=True)
    print(f'  N={N} one v for r=1/5 and r=1/2 (hence all r between): {count([K(F(1, 5)), K(F(1, 2))], N)}', flush=True)

def run_counterexample():
    arr = profile([F(1)]*7 + [F(6, 5)]*7, F(1, 2))
    assert linearization(*arr)[14][14][14] < 0
    return certify(arr, 14, 14, 14), certify(arr, 14, 14, 14, known='oneshot')

def run_maximum_principle(samples, rng_seed=5):
    """One-shot certificates at every deep point versus (P), on perturbed Krawtchouk arrays."""
    from random import Random
    rng = Random(rng_seed); agree = disagree = 0; N = 6
    while agree + disagree < samples:
        d = [F(0)]
        for i in range(N): d.append(d[-1] + F(rng.randint(5, 12)))
        d = [x/d[-1] for x in d]; r = F(rng.randint(1, 10), 10)
        c = [r*x for x in d]
        b = [max(F(0), (1-r)*x + F(rng.randint(-2, 2), 100)*x*(1-x)) for x in d]
        a = [1-x-y for x, y in zip(b, c)]
        if any(x <= 0 for x in a[:N]): continue
        a[N] = F(0)
        g = linearization(a, b, c)
        P = all(x >= 0 for G in g for row in G for x in row)
        MP = all(certify((a, b, c), *t, known='oneshot') for t in deep_points(N))
        if P == MP: agree += 1
        else: disagree += 1
    return agree, disagree

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--samples', type=int, default=60)
    args = parser.parse_args()
    for N in [4, 6]:
        for r in [F(1, 2), F(1, 5)]:
            print(f'tilted reversal N={N} r={r}: T=W trivial; T=W(r=1) gives min UT = {tilted_reversal(N, r)}')
    for rs in [[F(1, 2)]*4, [F(1, 2)]*3 + [F(2, 5)], [F(3, 10), F(1, 2), F(7, 10), F(9, 10)]]:
        print(f'site-dependent r_j={[str(x) for x in rs]}: {site_dependent_values(rs)} values (N+1={len(rs)+1})')
    print('bias scan N=14 profile (r, #negative):', [(str(r), n) for r, n in bias_scan()])
    for N in [6, args.max_n]:
        for r in [F(1), F(1, 2), F(1, 5)]:
            good, tot, worst = run_marching(N, r)
            print(f'marching Riemann function N={N} r={r}: nonnegative flux at {good}/{tot}; flux at (N,N,1) reaches {worst}')
    try:
        import scipy  # noqa: F401
    except ImportError:
        print('scipy not available; skipping linear programs'); return
    for N in [5, args.max_n]:
        run_lp(N)
    print('N=14 counterexample, certificate at the negative point (induction, one-shot):', run_counterexample())
    print('one-shot certificates vs (P) on perturbed arrays (agree, disagree):', run_maximum_principle(args.samples))

if __name__ == '__main__':
    main()
