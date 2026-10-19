"""Exact diagnostics for Szwarc's quadratic system (Section 7); not a proof."""
from fractions import Fraction as F
from itertools import combinations
from random import Random
from probe import linearization

def szwarc_array(N, p0):
    """Stochastic form (7.2) of Szwarc's recurrence, indices 0..2N."""
    a, b, c = [], [], []
    for k in range(2*N+1):
        if k % 2 == 0:
            n = k//2
            a.append(F(N-n, N)); c.append(F(n, N))
        else:
            a.append(1-p0); c.append(p0)
        b.append(F(0))
    return a, b, c

def on_support(m, n, k):
    return abs(m-n) <= k <= m+n and (m+n+k) % 2 == 0

# --- graded model of Lemmas 7.2-7.3 --------------------------------------
def a_mul(u, v, r):
    """Product in A: y_j^2=(1-r)y_j+r; elements are dicts frozenset->Fraction."""
    out = {}
    for S, x in u.items():
        for T, y in v.items():
            terms = {S ^ T: x*y}
            for j in S & T:
                new = {}
                for U, cf in terms.items():
                    new[U | {j}] = new.get(U | {j}, 0) + cf*(1-r)
                    new[U] = new.get(U, 0) + cf*r
                terms = new
            for U, cf in terms.items():
                out[U] = out.get(U, 0) + cf
    return {U: x for U, x in out.items() if x != 0}

def a_add(u, v, s=1):
    out = dict(u)
    for U, x in v.items():
        out[U] = out.get(U, 0) + s*x
    return {U: x for U, x in out.items() if x != 0}

def graded_model(N, r):
    """Vectors of V as (even part in A, tuple of N coordinates in A)."""
    f = [{frozenset(): r/(1+r), frozenset([l]): 1/(1+r)} for l in range(N)]
    zero = {}
    def U(k):
        if k % 2 == 0:
            n = k//2
            w = F(1, len(list(combinations(range(N), n))))
            return ({frozenset(S): w for S in combinations(range(N), n)}, tuple(zero for _ in range(N)))
        n = k//2
        coords = []
        for l in range(N):
            rest = [i for i in range(N) if i != l]
            sets = list(combinations(rest, n))
            w = F(1, len(sets))
            coords.append(a_mul(f[l], {frozenset(S): w for S in sets}, r))
        return (zero, tuple(coords))
    def Y(vec):
        u, v = vec
        even = {}
        for l in range(N):
            even = a_add(even, v[l], F(1, N))
        return (even, tuple(a_mul(f[l], u, r) for l in range(N)))
    def act(x, vec):            # A-action of x in A
        u, v = vec
        return (a_mul(x, u, r), tuple(a_mul(x, w, r) for w in v))
    def comb(terms):
        even, coords = {}, [{} for _ in range(N)]
        for cf, (u, v) in terms:
            even = a_add(even, u, cf)
            for l in range(N):
                coords[l] = a_add(coords[l], v[l], cf)
        return (even, tuple(coords))
    return f, U, Y, act, comb

def check_graded(N, p0):
    r = p0/(1-p0)
    f, U, Y, act, comb = graded_model(N, r)
    for l in range(N):
        assert a_mul(f[l], f[l], r) == f[l]
        assert a_mul({frozenset([l]): F(1)}, f[l], r) == f[l]
    a, b, c = szwarc_array(N, p0)
    M = 2*N
    Us = [U(k) for k in range(M+1)]
    for k in range(M+1):
        terms = []
        if k < M: terms.append((a[k], Us[k+1]))
        if k > 0: terms.append((c[k], Us[k-1]))
        assert Y(Us[k]) == comb(terms), (N, p0, k)
    g = linearization(a, b, c)
    for m in range(0, M+1, 2):            # U_m U_n = sum_k g(m,n;k) U_k for even m
        for n in range(M+1):
            assert act(Us[m][0], Us[n]) == comb([(g[m][n][k], Us[k]) for k in range(M+1) if g[m][n][k]]), (N, p0, m, n)

def run(max_n, perturbations, rng_seed=411):
    count = 0
    for N in range(1, max_n+1):
        for p0 in [F(1,10), F(1,5), F(1,3), F(2,5), F(9,20), F(1,2)]:
            a, b, c = szwarc_array(N, p0)
            M = 2*N
            g = linearization(a, b, c)
            r = p0/(1-p0); s = min(r, 1-r); delta = (r*s/8)**N
            for m in range(M+1):
                for n in range(M+1):
                    assert sum(g[m][n]) == 1 and g[m][n] == g[n][m]
                    for k in range(M+1):
                        x = g[m][n][k]
                        if on_support(m, n, k):
                            assert x >= delta, (N, p0, m, n, k)
                        else:
                            assert x == 0, (N, p0, m, n, k)
            count += 1
        for p0 in [F(3,5), F(9,10)]:
            a, b, c = szwarc_array(N, p0)
            r = p0/(1-p0)
            assert linearization(a, b, c)[2][2][2] == (1-r)/N < 0
        print(f'N={N}: Szwarc arrays (P) with margin (rs/8)^N, sharp at p0>1/2; cumulative={count}', flush=True)
    for N in range(1, min(max_n, 4)+1):
        for p0 in [F(1,5), F(2,5), F(1,2), F(3,4)]:
            check_graded(N, p0)
        print(f'N={N}: graded model identities (Lemmas 7.2-7.3, product mechanism) verified', flush=True)
    rng = Random(rng_seed)
    pert = 0
    for N in range(1, min(max_n, 3)+1):
        for p0 in [F(1,5), F(2,5)]:
            r = p0/(1-p0); s = min(r, 1-r)
            eta = F(1,2)*(r*s/8)**N/(16*N)**(2*N)
            margin = F(1,2)*(r*s/8)**N
            for sample in range(perturbations):
                a, b, c = szwarc_array(N, p0)
                for k in range(1, 2*N):
                    c[k] += F(rng.randint(-4, 4), 4)*eta
                    a[k] = 1 - c[k]
                g = linearization(a, b, c)
                M = 2*N
                for m in range(M+1):
                    for n in range(M+1):
                        assert sum(g[m][n]) == 1
                        for k in range(M+1):
                            if on_support(m, n, k):
                                assert g[m][n][k] >= margin
                            else:
                                assert g[m][n][k] == 0
                pert += 1
        print(f'N={N}: symmetric perturbations keep margin; cumulative={pert}', flush=True)
    return count, pert

# --- Theorem 7.8 and Corollary 7.9 ----------------------------------------
def qint(n, q):
    return sum((q**j for j in range(n)), F(0))

def geometric(N, q, r):
    d = [qint(i, q)/qint(N, q) for i in range(N+1)]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def parity_split_array(N, q, p0):
    """Symmetric array of Corollary 7.9: c_{2n}=[n]_q/[N]_q, c_{2n+1}=p0."""
    a, c = [], []
    for k in range(2*N+1):
        x = qint(k//2, q)/qint(N, q) if k % 2 == 0 else p0
        c.append(x); a.append(1-x)
    return a, [F(0)]*(2*N+1), c

def components(a, c):
    """Normalized even and odd components of Theorem 7.8."""
    M = len(a)-1; N = M//2
    A = lambda k: a[k] if 0 <= k <= M else F(0)
    C = lambda k: c[k] if 0 <= k <= M else F(0)
    even = ([A(2*n)*A(2*n+1) for n in range(N+1)],
            [C(2*n)*A(2*n-1)+A(2*n)*C(2*n+1) for n in range(N+1)],
            [C(2*n)*C(2*n-1) for n in range(N+1)])
    odd = ([A(2*n+1)*A(2*n+2) for n in range(N)],
           [A(2*n+1)*C(2*n+2)+C(2*n+1)*A(2*n) for n in range(N)],
           [C(2*n+1)*C(2*n) for n in range(N)])
    def normalize(u, dg, l):
        return [x/u[0] for x in u], [(x-dg[0])/u[0] for x in dg], [x/u[0] for x in l]
    return normalize(*even), normalize(*odd)

def check_decomposition(a, c):
    """Verify the coefficient formulas of Theorem 7.8 for one symmetric array."""
    N = (len(a)-1)//2
    g = linearization(a, [F(0)]*len(a), c)
    even, odd = components(a, c)
    ge, go = linearization(*even), linearization(*odd)
    for x in range(N+1):
        for y in range(N+1):
            for z in range(N+1):
                assert g[2*x][2*y][2*z] == ge[x][y][z]
        for y in range(N):
            for z in range(N):
                expected = (a[2*x]*go[x][y][z] if x < N else 0) + (c[2*x]*go[x-1][y][z] if x > 0 else 0)
                assert g[2*x][2*y+1][2*z+1] == expected
    return g

def run_decomposition(max_n, perturbations, rng_seed=713):
    count = 0
    rng = Random(rng_seed)
    for N in range(2, max_n+1):
        for q in [F(1), F(3,2), F(2)]:
            for p0 in [F(1,5), F(2,5), F(1,2)]:
                r = p0/(1-p0)
                a, b, c = parity_split_array(N, q, p0)
                even, odd = components(a, c)
                assert even == geometric(N, q, r) and odd == geometric(N-1, q, r/q)
                g = check_decomposition(a, c)
                assert all(x >= 0 for G in g for row in G for x in row)
                count += 1
            a, b, c = parity_split_array(N, q, F(3,5))
            assert linearization(a, b, c)[2][2][2] < 0
        for sample in range(perturbations):     # formulas on generic symmetric arrays
            c = [F(0)] + [F(rng.randint(1, 9), 10) for _ in range(2*N-1)] + [F(1)]
            a = [1-x for x in c]
            check_decomposition(a, c)
        print(f'N={N}: parity-split arrays (P), components geometric(N,q,r), geometric(N-1,q,r/q); decomposition formulas exact; cumulative={count}', flush=True)
    return count

def convex_counterexamples():
    """Section 8: convex profiles with constant ratio fail at the terminal product."""
    out = []
    cases = [(14, [F(1)]*7 + [F(6,5)]*7, F(1,2)), (20, [F(1)]*12 + [F(21,20)]*8, F(2,5)),
             (18, [F(1)]*14 + [F(21,20)**t for t in range(1,5)], F(1,2))]
    for N, inc, r in cases:
        d = [F(0)]
        for x in inc: d.append(d[-1]+x)
        d = [x/d[-1] for x in d]
        g = linearization([1-x for x in d], [(1-r)*x for x in d], [r*x for x in d])
        assert g[N][N][N] < 0
        out.append((N, r, g[N][N][N]))
    return out
