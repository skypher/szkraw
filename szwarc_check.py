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
