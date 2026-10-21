# Review round 10 (scoped): sign-pattern shape criteria in Section 9

You reviewed this paper in nine rounds; the last (round 9) confirmed the Section 9 nonconvexity passage. One new passage was added to Section 9 ("Monotonicity-type criteria for finite systems"), directly after that passage. Source: commit 29e89fce304b55b736ce6c4a85f42821e823c344 (github.com/skypher/szkraw), paper.tex SHA-256 bd11c30346c5ab44380e8a445ee93a0493076e1db8100cd869f1a572e3a7ccf6.

## New passage

```tex
Sign conditions on the shape fail in the same way. Write $d_n=b_n+c_n$ and $\rho_n=c_n/d_n$ for $n\geq1$. For $S_1,S_2\in\{[0,\infty),(-\infty,0],\{0\},\mathbb R\}$ and $\rho_{\max}>0$, consider the stochastic arrays with $b_0=0$, $a_n$ decreasing, $b_n$ and $c_n$ nondecreasing, $d_{n+2}-2d_{n+1}+d_n\in S_1$ for $0\leq n\leq N-2$, $\rho_{n+1}-\rho_n\in S_2$ for $1\leq n\leq N-1$, and $\rho_n\leq\rho_{\max}$. Each such class contains every $K_{N,r}$ with $r\leq\rho_{\max}$, and for $S_1=S_2=\{0\}$ it consists of these arrays only. For every other choice of $(S_1,S_2)$ and every $\rho_{\max}\geq83/400$, exact computation (\path{signpattern_probe.py}) gives an array in the class with $g(N,N;N)<0$. If $S_1$ contains a positive number, take constant ratio $1/5$ and eighty unit increments followed by twenty increments $11/10$ ($N=100$). If $S_1$ contains a negative number, take constant ratio $1/10$ and seventeen unit increments followed by three increments $1/2$ ($N=20$). If $S_1=\{0\}$ and $S_2$ contains a positive number, take $d_n=n/N$ and $\rho_n=1/5+\max(n-102,0)/2400$ ($N=120$). If $S_1=\{0\}$ and $S_2$ contains a negative number, take $d_n=n/N$ and $\rho_n=1/5-\max(n-68,0)/1600$ ($N=80$). Thus, apart from the Krawtchouk family itself, no sufficient criterion for property (P) consists of these sign conditions alone. For $\rho_{\max}<83/400$ these four examples do not all lie in the class, and the statement is open; for instance, with $S_1=\{0\}$ and increasing ratio starting from $\rho=1/10$, our search found no failure for $N\leq300$. Criteria with conditions on higher differences, with mixed conditions, or with conditions that do not apply at every index are not covered.
```

Notation: stochastic arrays satisfy a_n + b_n + c_n = 1, a_0 = 1, b_0 = c_0 = 0, a_N = 0, a_n > 0 (n < N), c_n > 0 (n > 0), b_n >= 0. Property (P) is nonnegativity of every linearization coefficient g(m,n;k); the witness is the corner g(N,N;N), computed by the paper's column-N recurrence in exact rational arithmetic (function corner() in smallr_probe.py). K_{N,r} has a_n = 1 - n/N, b_n = (1-r)n/N, c_n = rn/N, i.e. d_n = n/N and rho_n = r.

Please check:
1. The case analysis: for (S_1,S_2) != ({0},{0}), each class contains one of the four arrays (S_2 always contains 0, so constant-ratio arrays satisfy every S_2; S_1 = {0} forces the linear profile). Are the four arrays in the stated classes (including monotone a, b, c and rho <= 83/400)?
2. The exact signs g(N,N;N) < 0 (please recompute independently, at least the N = 20 and N = 80 cases).
3. Scope: is "no sufficient criterion for property (P) consists of these sign conditions alone, apart from the Krawtchouk family" correctly stated, given the rho_max >= 83/400 restriction and the listed exclusions? Is the claim that for S_1 = S_2 = {0} the class "consists of these arrays only" (the Krawtchouk arrays K_{N,r}, r <= rho_max) correct?
4. Verdict: PASS, PASS WITH MINOR FIXES, or FAIL, with replacement text for any fix.

Keep the answer short if everything is in order.

## Script signpattern_probe.py

```python
"""Sign-pattern shape criteria (Section 9); exact, diagnostics.

Write d_n = b_n + c_n and rho_n = c_n/d_n (n >= 1). For S1, S2 in {[0,inf), (-inf,0], {0}, R}, the class C(S1, S2, rho_max)
consists of the stochastic arrays (b_0 = 0) with a_n decreasing, b_n and c_n nondecreasing, d_{n+2} - 2 d_{n+1} + d_n in S1
(0 <= n <= N-2), rho_{n+1} - rho_n in S2 (1 <= n <= N-1) and rho_n <= rho_max. It contains every K(N,r) with r <= rho_max;
for S1 = S2 = {0} it is the Krawtchouk family. For every other (S1, S2) and rho_max >= 83/400 one of the four arrays below
lies in the class and has g(N,N;N) < 0 in exact arithmetic:
  convex   (S1 has a positive element): constant ratio 1/5, 80 unit increments then 20 increments 11/10, N = 100;
  concave  (S1 has a negative element): constant ratio 1/10, 17 unit increments then 3 increments 1/2, N = 20;
  rising   (S1 = {0}, S2 has a positive element): d_n = n/N, rho_n = 1/5 + max(n-102, 0)/2400, N = 120 (max 83/400);
  falling  (S1 = {0}, S2 has a negative element): d_n = n/N, rho_n = 1/5 - max(n-68, 0)/1600, N = 80.
"""
import argparse
import time
from fractions import Fraction as F
from smallr_probe import corner

def from_profile(inc, rho):
    d = [F(0)]
    for x in inc: d.append(d[-1] + x)
    d = [x/d[-1] for x in d]
    return [1 - x for x in d], [(1 - p)*x for p, x in zip(rho, d)], [p*x for p, x in zip(rho, d)], d

def examples():
    yield 'convex', 100, from_profile([F(1)]*80 + [F(11, 10)]*20, [F(1, 5)]*101)
    yield 'concave', 20, from_profile([F(1)]*17 + [F(1, 2)]*3, [F(1, 10)]*21)
    yield 'rising', 120, from_profile([F(1)]*120, [F(1, 5) + F(max(n - 102, 0), 2400) for n in range(121)])
    yield 'falling', 80, from_profile([F(1)]*80, [F(1, 5) - F(max(n - 68, 0), 1600) for n in range(81)])

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    for name, N, (a, b, c, d) in examples():
        t0 = time.time()
        rho = [c[n]/d[n] for n in range(1, N+1)]
        basic = (a[0] == 1 and b[0] == 0 and a[N] == 0 and all(x > 0 for x in a[:N]) and all(x > 0 for x in c[1:])
                 and all(x >= 0 for x in b) and all(a[n] + b[n] + c[n] == 1 for n in range(N+1)))
        mono = all(a[n+1] < a[n] and b[n+1] >= b[n] and c[n+1] >= c[n] for n in range(N))
        d2 = [d[n+2] - 2*d[n+1] + d[n] for n in range(N-1)]; dr = [rho[i+1] - rho[i] for i in range(N-1)]
        signs = lambda v: ('+' if any(x > 0 for x in v) else '') + ('-' if any(x < 0 for x in v) else '') or '0'
        g = corner(a, b, c)
        print(f'{name}: N={N}; basic conditions {basic}; a decreasing, b and c nondecreasing {mono}; '
              f'signs of second differences of d: {signs(d2)}; signs of differences of rho: {signs(dr)}; max rho {max(rho)}; '
              f'g(N,N;N) = {float(g):+.4e} ({time.time()-t0:.0f}s)', flush=True)

if __name__ == '__main__':
    main()

```

## Output of python3 signpattern_probe.py

```
convex: N=100; basic conditions True; a decreasing, b and c nondecreasing True; signs of second differences of d: +; signs of differences of rho: 0; max rho 1/5; g(N,N;N) = -2.4653e-09 (0s)
concave: N=20; basic conditions True; a decreasing, b and c nondecreasing True; signs of second differences of d: -; signs of differences of rho: 0; max rho 1/10; g(N,N;N) = -4.2414e-02 (0s)
rising: N=120; basic conditions True; a decreasing, b and c nondecreasing True; signs of second differences of d: 0; signs of differences of rho: +; max rho 83/400; g(N,N;N) = -1.0314e-11 (0s)
falling: N=80; basic conditions True; a decreasing, b and c nondecreasing True; signs of second differences of d: 0; signs of differences of rho: -; max rho 1/5; g(N,N;N) = -1.1766e-08 (0s)
```
