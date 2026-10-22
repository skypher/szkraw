# Explore the dual certificate Z for Lemma 9.2 at K_{N,1}: Z J - J Z + y e_0^T = e_N e_N^T.
from fractions import Fraction as F
from math import comb
import sys

def kraw_R(N):
    # R_n(lambda_j) for K_{N,1}: lambda_j = 1-2j/N, R via recurrence
    a = [F(N-n, N) for n in range(N+1)]; c = [F(n, N) for n in range(N+1)]
    R = [[F(0)]*(N+1) for _ in range(N+1)]  # R[n][j]
    for j in range(N+1):
        lam = 1 - F(2*j, N)
        R[0][j] = F(1)
        if N >= 1: R[1][j] = lam
        for n in range(1, N):
            R[n+1][j] = (lam*R[n][j] - c[n]*R[n-1][j]) / a[n]
    return R

def Zmat(N):
    R = kraw_R(N)
    w = [F(comb(N, j), 2**N) for j in range(N+1)]
    pi = [comb(N, n) for n in range(N+1)]
    Z = [[F(0)]*(N+1) for _ in range(N+1)]
    for m in range(N+1):
        for n in range(N+1):
            s = F(0)
            for i in range(N+1):
                for j in range(N+1):
                    if (i+j) % 2 == 1:
                        s += R[m][i]*w[i]*w[j]*R[n][j]/(i-j)
            Z[m][n] = -N*pi[n]*s
    return Z

if __name__ == "__main__":
  for N in range(2, int(sys.argv[1]) + 1):
      Z = Zmat(N)
      print("N =", N)
      for row in Z:
          print("  ", [str(x) for x in row])
      W = [[Z[m][N-n] - Z[N-m][n] for n in range(N+1)] for m in range(N+1)]
      print(" W:")
      for row in W:
          print("  ", [str(x) for x in row])
