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
