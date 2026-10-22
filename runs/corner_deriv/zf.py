from zcert import Zmat
from math import comb
import sys
for N in range(2, int(sys.argv[1])+1):
    Z = Zmat(N)
    print("N =", N)
    for m in range(N+1):
        print("  ", [str(Z[m][n]/comb(N,n)) if (m+n)%2 else '.' for n in range(N+1)])
