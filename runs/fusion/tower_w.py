"""Positive triangular fusion algebras with weighted level sums.
Algebra over Q[u,v]: generators z_1..z_N, relations z_j^2 = f_j with
  f_j = sum_{j<=a<b} lam[j,a,b] z_a z_b + u sum_{a>=j} mu[j,a] z_a + v nu[j],  all coefficients >= 0.
Leading terms z_j^2 are coprime, so the relations are a Groebner basis (lex z_1 > ... > z_N): squarefree monomials z_S are a
basis, the algebra is commutative and associative, and its structure constants are in R>=0[u,v].
Target: P_k = sum_{|S|=k} w_S z_S (w > 0) with P_0 = 1, P_1 = X and
  X P_k = a_k P_{k+1} + u d_k P_k + v d_k P_{k-1},  a_k = 1 - d_k,  d = profile (d_N = 1).
Then g(m,n;k) are coefficientwise nonnegative in (u, v) (read off any z_S in the support of P_k), i.e. (Gamma) holds.
Search: nonlinear least squares with bounds >= 0 from random starts; report the best residual."""
import sys, itertools, random, time
import numpy as np, sympy as sp
from scipy.optimize import least_squares

def build(N):
    u, v = sp.symbols('u v')
    idx = range(1, N+1)
    lam = {(j, a, b): sp.Symbol(f'l_{j}_{a}_{b}') for j in idx for a in range(j, N+1) for b in range(a+1, N+1)}
    mu = {(j, a): sp.Symbol(f'm_{j}_{a}') for j in idx for a in range(j, N+1)}
    nu = {j: sp.Symbol(f'n_{j}') for j in idx}
    subsets = [frozenset(S) for k in range(N+1) for S in itertools.combinations(idx, k)]
    w = {S: (sp.Integer(1) if len(S) == 0 else sp.Symbol('w_' + ''.join(map(str, sorted(S))))) for S in subsets}
    cache = {}
    def mul_gen(j, S):
        """z_j * z_S as dict frozenset -> sympy coefficient (polynomial in u, v and unknowns)."""
        key = (j, S)
        if key in cache: return cache[key]
        if j not in S: res = {S | {j}: sp.Integer(1)}
        else:
            R = S - {j}; res = {}
            def add(dct, c):
                for T, x in dct.items(): res[T] = res.get(T, 0) + c*x
            for (jj, a, b), c in lam.items():
                if jj != j: continue
                add(mul_mono([a, b], R), c)
            for (jj, a), c in mu.items():
                if jj != j: continue
                add(mul_mono([a], R), u*c)
            add({R: sp.Integer(1)}, v*nu[j])
        cache[key] = res; return res
    def mul_mono(gens, S):
        cur = {S: sp.Integer(1)}
        for g in gens:
            nxt = {}
            for T, x in cur.items():
                for U, y in mul_gen(g, T).items(): nxt[U] = nxt.get(U, 0) + x*y
            cur = nxt
        return cur
    unknowns = list(lam.values()) + list(mu.values()) + list(nu.values()) + [w[S] for S in subsets if len(S) > 0]
    return u, v, lam, mu, nu, w, subsets, mul_gen, unknowns

def equations(N, d):
    u, v, lam, mu, nu, w, subsets, mul_gen, unknowns = build(N)
    P = {k: {S: w[S] for S in subsets if len(S) == k} for k in range(N+1)}
    eqs = []
    for k in range(N+1):
        lhs = {}
        for S, ws in P[k].items():
            for j in range(1, N+1):
                for T, c in mul_gen(j, S).items(): lhs[T] = lhs.get(T, 0) + w[frozenset({j})]*ws*c
        rhs = {}
        def add(Pk, c):
            for T, x in Pk.items(): rhs[T] = rhs.get(T, 0) + c*x
        if k < N: add(P[k+1], 1 - d[k])
        add(P[k], u*d[k])
        if k > 0: add(P[k-1], v*d[k])
        for T in set(lhs) | set(rhs):
            e = sp.expand(lhs.get(T, 0) - rhs.get(T, 0))
            for mon, c in sp.Poly(e, u, v).terms():
                if c != 0: eqs.append(c)
    return eqs, unknowns

def solve(N, d, starts=200, seed=0):
    eqs, unk = equations(N, [sp.nsimplify(x) for x in d])
    f = sp.lambdify(unk, eqs, 'numpy')
    J = sp.lambdify(unk, sp.Matrix(eqs).jacobian(unk), 'numpy')
    rng = np.random.default_rng(seed); best = None
    for _ in range(starts):
        x0 = rng.exponential(1.0, len(unk))
        r = least_squares(lambda x: np.array(f(*x), dtype=float), x0, jac=lambda x: np.array(J(*x), dtype=float),
                          bounds=(0, np.inf), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        if best is None or r.cost < best[0]: best = (r.cost, r.x)
        if best[0] < 1e-26: break
    return best, unk

def profile(N, sig):
    D = [sum(sp.binomial(n, k)*sig[k-1] for k in range(1, n+1)) for n in range(N+1)]
    return [sp.Rational(x)/D[N] for x in D]

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    tests = [('Krawtchouk', [1, 0, 0, 0, 0][:N]), ('geometric q=2', [1, 1, 1, 1, 1][:N]), ('geometric q=3/2', [1, sp.Rational(1, 2), sp.Rational(1, 4), sp.Rational(1, 8)][:N]),
             ('Q x=1/2', [1, sp.Rational(1, 2), 0, 0][:N]), ('Q x=1', [1, 1, 0, 0][:N]), ('LC 1,1/2,1/8', [1, sp.Rational(1, 2), sp.Rational(1, 8), sp.Rational(1, 64)][:N]),
             ('log-convex 1,1/2,1/2', [1, sp.Rational(1, 2), sp.Rational(1, 2), sp.Rational(1, 2)][:N])]
    for name, sig in tests:
        t0 = time.time(); (cost, x), unk = solve(N, profile(N, sig))
        print(f'N={N} {name:22s}: best residual {2*cost:.2e} ({len(unk)} unknowns, {time.time()-t0:.0f}s)', flush=True)
