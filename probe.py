"""Exact small finite recurrence probes; diagnostics, not a proof."""
import argparse
from fractions import Fraction as F

def linearization(a, b, c):
    """Matrices R_m(J), with row n equal to product coefficients of R_m R_n."""
    size = len(a)
    ident = [[F(i == j) for j in range(size)] for i in range(size)]
    zero = [[F(0) for j in range(size)] for i in range(size)]
    result = [ident]
    previous, current = zero, ident
    for m in range(size - 1):
        following = []
        for i in range(size):
            row = []
            for j in range(size):
                entry = (b[i] - b[m]) * current[i][j] - c[m] * previous[i][j]
                if i:
                    entry += c[i] * current[i-1][j]
                if i + 1 < size:
                    entry += a[i] * current[i+1][j]
                row.append(entry / a[m])
            following.append(row)
        result.append(following)
        previous, current = current, following
    return result

def first_negative(matrices):
    return next(((m,n,k,x) for m,mat in enumerate(matrices)
                 for n,row in enumerate(mat) for k,x in enumerate(row) if x < 0), None)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6)
    args = parser.parse_args()
    for N in range(2, args.max_n + 1):
        for exponent in [1,2,3]:
            for r in [F(1), F(1,2), F(1,5)]:
                d = [F(i,N)**exponent for i in range(N+1)]
                a = [1-x for x in d]
                b = [(1-r)*x for x in d]
                c = [r*x for x in d]
                neg = first_negative(linearization(a,b,c))
                print(f'N={N} exponent={exponent} r={r} negative={neg}', flush=True)

if __name__ == '__main__':
    main()
