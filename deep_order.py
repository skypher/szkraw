"""Exact probes of Krawtchouk deep coefficients near the symmetric endpoint; diagnostics, not a proof.

1. Order of vanishing of g(m,n;k) as r -> 1 at every deep triple, compared with
   max(m+n+k-2N, (m+n+k) mod 2).
2. Sign of the change of each deep coefficient when the top diagonal is raised
   (b_N up, c_N down) or row N-1 is moved the same way.
"""
import argparse
import math
from fractions import Fraction as F
from probe import linearization

def kraw(N, r):
    d = [F(i, N) for i in range(N+1)]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def deep(N):
    return [(m,n,k) for m in range(N+1) for n in range(m, N+1) for k in range(N+1)
            if m+n > N and m+k > N and n+k > N]

def vanishing_order(N):
    e1, e2 = F(1, 10**3), F(1, 10**4)
    g1, g2 = linearization(*kraw(N, 1-e1)), linearization(*kraw(N, 1-e2))
    mismatches = []
    for m, n, k in deep(N):
        x1, x2 = g1[m][n][k], g2[m][n][k]
        order = math.inf if x1 == 0 == x2 else round(math.log10(float(x1/x2)))
        expect = max(m+n+k-2*N, (m+n+k) % 2)
        if order != expect:
            mismatches.append((m, n, k, order, expect))
    return len(deep(N)), mismatches

def top_row_signs(N, r, row):
    h = F(1, 10**6)
    a, b, c = kraw(N, r)
    g0 = linearization(a, b, c)
    b1, c1 = b[:], c[:]
    b1[row] += h
    c1[row] -= h
    g1 = linearization(a, b1, c1)
    diff = [g1[m][n][k]-g0[m][n][k] for m, n, k in deep(N)]
    return sum(x > 0 for x in diff), sum(x < 0 for x in diff), sum(x == 0 for x in diff)

def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--sizes', type=int, nargs='+', default=[5, 6, 8])
    args = parser.parse_args()
    for N in args.sizes:
        total, mismatches = vanishing_order(N)
        print(f'N={N}: vanishing order matches at {total-len(mismatches)}/{total} deep triples; '
              f'mismatches {mismatches[:6]}', flush=True)
        for r in (F(1,5), F(1,2), F(9,10)):
            up, down, zero = top_row_signs(N, r, N)
            up1, down1, zero1 = top_row_signs(N, r, N-1)
            print(f'  r={r}: raise b_N: +{up} -{down} 0:{zero}; raise b_(N-1): +{up1} -{down1} 0:{zero1}',
                  flush=True)

if __name__ == '__main__':
    main()
