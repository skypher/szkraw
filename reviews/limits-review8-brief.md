# Review round 8 (scoped): confirmation of the round-7 fix and a new Section 9 passage

You reviewed this paper in seven rounds. Round 7 (commit b65fcad) returned PASS WITH MINOR FIXES for the terminal-row correction. This round has two items. Source: commit d87857f4df168a32e3b619bb319551365ff4a838 (repository github.com/skypher/szkraw), paper.tex SHA-256 dfc2aec612fa8a03ca1a253f6d3fc32a265309c30c6f88885b52071b828a827d; the two passages are quoted in full below.

## Item 1: your round-7 fix

Your replacement text for the opening of the final sentence of the remark after Corollary 8.13 was applied verbatim. The passage now reads:

```tex
At $r=\tfrac12$, computations for $N=30,\ldots,77$, using maxima over successive six-size windows, give estimated envelope decay factors $0.503,0.593,0.640,0.676$ for the absolute Taylor coefficients of orders $1,2,3,4$, respectively. This is a finite-range computational observation, not an asymptotic statement. Exact terminal-row failures also occur for $r\leq\tfrac12$: at size $6.3\cdot10^{-6}$ for $r=\tfrac12$, $N=120$; at size $3.2\cdot10^{-3}$ for $r=\tfrac25$, $N=100$; and at size $1.6\cdot10^{-2}$ for $r=\tfrac13$, $N=120$.
```

Please confirm it is applied correctly.

## Item 2: new passage in Section 9 ("Monotonicity-type criteria for finite systems"), after the sentence "Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$."

```tex
Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. A criterion given by linear inequalities in the coefficients admits a convex set of arrays, but property (P) at fixed $(N,r)$ is not convex, even between arrays admitted by Theorem~\ref{thm:criterion}. For $q\geq1$ let $G_{N,q,r}$ be the array \eqref{eq:parameters}, so that $G_{N,1,r}=K_{N,r}$. For $0<\lambda<1$ the combination $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ is a stochastic array with constant ratio $b_i/c_i$ and increments proportional to $1+t\,q^{i-N}$, where $t=\lambda(q^N-1)/((1-\lambda)N(q-1)q^{N-1})$. Exact computation (\path{convexity_probe.py}) gives $g(N,N;N)<0$ for this combination at $(r,N,q,t)=(4/5,10,10,1)$, $(3/5,20,10,2)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$, $(1/3,100,10,2)$, $(3/10,200,2,5)$ and $(2/7,200,10,5)$. Computations in $150$- and $300$-digit arithmetic agree on $g(N,N;N)<0$ at $(1/4,500,3,10)$; this is not an exact sign certificate. Hence, at these sizes, no criterion whose admitted set is convex, in particular no system of linear inequalities in the coefficients, admits both $K_{N,r}$ and $G_{N,q,r}$. The sizes at which we found such failures grow as $r$ decreases; at $r=1/5$ none was found on our grid of values of $q$ and $t$ for $N\leq1000$.
```

Notation: $K_{N,r}$ has $a_i=1-i/N$, $b_i=(1-r)i/N$, $c_i=ri/N$. Equation (eq:parameters) is the coefficient parametrization of Theorem 2.1 (Lemma 2.2): $a_i=q^i[N-i]_q/[N]_q$, $b_i=(1-r)[i]_q/[N]_q$, $c_i=r[i]_q/[N]_q$, $q\geq1$, $0<r\leq1$. Theorem 2.1 (geometric increment criterion) proves property (P) for these arrays. Property (P) is nonnegativity of all linearization coefficients $g(m,n;k)$; the witness here is the corner $g(N,N;N)$, computed by the paper's recurrence (column $N$ of the product table) in exact rational arithmetic (function corner() in smallr_probe.py, reproduced in the listing below by import).

Please check:
1. The algebra: the convex combination is stochastic with $b_0=0$, constant ratio $b_i/c_i=(1-r)/r$, and increments proportional to $1+t\,q^{i-N}$ with the stated $t$.
2. The exact sign claims (please recompute at least the smaller cases independently, e.g. $(4/5,10,10,1)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$), and whether the high-precision case $(1/4,500,3,10)$ is labelled appropriately.
3. The logical conclusion: a set of arrays cut out by linear (strict or non-strict) inequalities in the coefficients is convex, so it cannot contain both endpoints and have only arrays with (P), at the listed sizes. Is the statement "no criterion whose admitted set is convex ... admits both $K_{N,r}$ and $G_{N,q,r}$" correctly scoped?
4. The final sentence about growth of the sizes and the $r=1/5$ search is stated only as a computational observation. Is it worded acceptably?
5. Verdict for item 1 and item 2: PASS, PASS WITH MINOR FIXES, or FAIL, with replacement text for any fix.

Keep the answer short if everything is in order.

## Script convexity_probe.py (new)

```python
"""Nonconvexity of property (P) at fixed (N, r) (Section 9); exact, diagnostics.

K(N,r) = G(N,1,r) and the geometric array G(N,q,r) of (eq:parameters), q > 1, are both admitted by Theorem 2.1
(constant ratio b_i/c_i = (1-r)/r, geometric increments). The convex combination (1-lam) K + lam G is again a
stochastic constant-ratio array with b_0 = 0; its increments are proportional to 1 + t q^(i-N), not geometric, where
t = lam (q^N - 1)/((1-lam) N (q-1) q^(N-1)). For each listed (r, N, q, t) it has g(N,N;N) < 0 in exact arithmetic.
So no criterion whose admitted set is convex, such as a system of linear inequalities in the coefficients, admits
both K(N,r) and G(N,q,r) at these sizes.

Option --all adds the exact cases (3/10, 200, 2, 5) and (2/7, 200, 10, 5) (about 1 and 6 minutes) and the case
(1/4, 500, 3, 10) in 150- and 300-digit arithmetic (not an exact sign certificate). Option --scan R: high-precision
search (mpmath, 150 digits) over q in {3/2, 2, 3, 10} and t in {1/10, 3/10, 1/2, 1, 2, 5} for the smallest N on a
list with a negative corner on the segment.
"""
import argparse
import time
from fractions import Fraction as F
from smallr_probe import corner

EXAMPLES = [  # (r, N, q, t)
    (F(4, 5), 10, F(10), F(1)),
    (F(3, 5), 20, F(10), F(2)),
    (F(1, 2), 20, F(10), F(1)),
    (F(2, 5), 60, F(10), F(2)),
    (F(1, 3), 100, F(10), F(2)),
]
LARGE = [(F(3, 10), 200, F(2), F(5)), (F(2, 7), 200, F(10), F(5))]  # exact, about 1 and 6 minutes
HIGH_PRECISION = (F(1, 4), 500, 3, 10)  # 150 and 300 digits

def geometric(N, r, q):
    d = [F(0)]
    for i in range(1, N+1): d.append(d[-1] + q**(i-1))
    d = [x/d[-1] for x in d]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def combination(r, N, q, t):
    u = t*(q**N - 1)/(N*(q - 1)*q**(N-1)); lam = u/(1 + u)
    K, G = geometric(N, r, F(1)), geometric(N, r, q)
    return lam, K, G, [[(1-lam)*x + lam*y for x, y in zip(u, v)] for u, v in zip(K, G)]

def check(r, N, q, t):
    lam, K, G, (a, b, c) = combination(r, N, q, t)
    inc = [(a[i-1] - a[i])/(a[0] - a[1]) for i in range(1, N+1)]
    shape = all(inc[i]*(1 + t*q**(1-N)) == 1 + t*q**(i+1-N) for i in range(N))
    basic = (b[0] == 0 and a[N] == 0 and all(x > 0 for x in a[:N]) and all(x > 0 for x in c[1:])
             and all(x >= 0 for x in b) and all(a[n] + b[n] + c[n] == 1 for n in range(N+1))
             and all(b[n]*r == c[n]*(1-r) for n in range(N+1)))
    return lam, basic, shape, corner(*K), corner(*G), corner(a, b, c)

def corner_mp(a, b, c):
    import mpmath as mp
    N = len(a)-1
    prev = [mp.mpf(0)]*(N+1); cur = [mp.mpf(int(i == N)) for i in range(N+1)]
    for m in range(N):
        inv = 1/a[m]; nxt = []
        for i in range(N+1):
            v = (b[i]-b[m])*cur[i] - c[m]*prev[i]
            if i: v += c[i]*cur[i-1]
            if i < N: v += a[i]*cur[i+1]
            nxt.append(v*inv)
        prev, cur = cur, nxt
    return cur[N]

def segment_mp(r, N, q, t):
    import mpmath as mp
    rr = mp.mpf(r.numerator)/r.denominator
    inc = [1 + t*mp.mpf(q)**(i - N) for i in range(1, N+1)]
    d = [mp.mpf(0)]
    for x in inc: d.append(d[-1] + x)
    d = [x/d[-1] for x in d]
    return corner_mp([1-x for x in d], [(1-rr)*x for x in d], [rr*x for x in d])/(1-rr)**N

def scan(r, Ns):
    import mpmath as mp
    mp.mp.dps = 150
    for N in Ns:
        best = None
        for q in (mp.mpf(3)/2, 2, 3, 10):
            for t in (mp.mpf(1)/10, mp.mpf(3)/10, mp.mpf(1)/2, 1, 2, 5):
                g = segment_mp(r, N, q, t)
                if best is None or g < best[0]: best = (g, q, t)
        print(f'r={r} N={N}: min over the segment grid of g(N,N;N)/(1-r)^N = {mp.nstr(best[0], 5)} '
              f'(q={mp.nstr(best[1], 3)}, t={mp.nstr(best[2], 3)})', flush=True)
        if best[0] < 0: break

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--scan', type=F, help='bias r for the high-precision segment search')
    parser.add_argument('--all', action='store_true', help='also the N = 200 exact cases and the N = 500 high-precision case')
    parser.add_argument('--sizes', default='10,20,30,40,60,80,100,150,200,300')
    args = parser.parse_args()
    if args.scan is not None:
        scan(args.scan, [int(x) for x in args.sizes.split(',')]); return
    for r, N, q, t in EXAMPLES + (LARGE if args.all else []):
        t0 = time.time()
        lam, basic, shape, gK, gG, gA = check(r, N, q, t)
        print(f'r={r} N={N} q={q} t={t}: lambda={float(lam):.6g}; basic conditions and constant ratio {basic}; '
              f'increments proportional to 1+t*q^(i-N) {shape}; g(N,N;N) at K {float(gK):+.3e}, at G {float(gG):+.3e}, '
              f'at the combination {float(gA):+.3e} ({time.time()-t0:.0f}s)', flush=True)

    if args.all:
        import mpmath as mp
        r, N, q, t = HIGH_PRECISION
        for dps in (150, 300):
            mp.mp.dps = dps
            print(f'r={r} N={N} q={q} t={t}, {dps} digits: g(N,N;N)/(1-r)^N on the segment = '
                  f'{mp.nstr(segment_mp(r, N, q, t), 10)}', flush=True)

if __name__ == '__main__':
    main()

```

## Output of python3 convexity_probe.py --all

```
r=4/5 N=10 q=10 t=1: lambda=0.1; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +1.024e-07, at G +5.517e-01, at the combination -6.966e-04 (0s)
r=3/5 N=20 q=10 t=2: lambda=0.1; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +1.100e-08, at G +5.857e-01, at the combination -1.385e-04 (0s)
r=1/2 N=20 q=10 t=1: lambda=0.0526316; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +9.537e-07, at G +6.314e-01, at the combination -7.851e-06 (0s)
r=2/5 N=60 q=10 t=2: lambda=0.0357143; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +4.887e-14, at G +6.838e-01, at the combination -6.660e-10 (1s)
r=1/3 N=100 q=10 t=2: lambda=0.0217391; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +2.460e-18, at G +7.231e-01, at the combination -2.045e-15 (9s)
r=3/10 N=200 q=2 t=5: lambda=0.047619; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +1.046e-31, at G +5.778e-01, at the combination -1.498e-18 (47s)
r=2/7 N=200 q=10 t=5: lambda=0.027027; basic conditions and constant ratio True; increments proportional to 1+t*q^(i-N) True; g(N,N;N) at K +5.948e-30, at G +7.538e-01, at the combination -4.485e-22 (358s)
r=1/4 N=500 q=3 t=10, 150 digits: g(N,N;N)/(1-r)^N on the segment = -1.245457039e+23
r=1/4 N=500 q=3 t=10, 300 digits: g(N,N;N)/(1-r)^N on the segment = -1.245457039e+23
```
