"""Exact Λ_N of P3, proof of Proposition 9.8: Λ_N = max({0} ∪ {-A_z/B_z : z ∈ Z_N, A_z < 0}), where Z_N are the
triangle triples (m,n,k) with g(m,n;k) = 0 at K_{N,1}, A_z = ∂_ε g at (r,ε) = (1,0) for the array lowK N r ε of
lean/Szkraw/Interior.lean (top mass lowered by ε, fixed coordinate), and B_z = -∂_r g (rate of decreasing r).
Derivatives by exact first-order jets (value, derivative) through the product-table recurrence.
Usage: lambda_n.py [Nmax]"""
import sys
from fractions import Fraction as F
from math import comb

def jmul(x, y): return (x[0]*y[0], x[0]*y[1] + x[1]*y[0])
def jadd(x, y): return (x[0]+y[0], x[1]+y[1])
def jsub(x, y): return (x[0]-y[0], x[1]-y[1])
def jdiv(x, y): return (x[0]/y[0], (x[1]*y[0] - x[0]*y[1]) / (y[0]*y[0]))

def lowK_jets(N, which):
    """coefficients as jets at (1,0): which='e' differentiates in ε at r=1, 'r' in r at ε=0."""
    def A(n):  # lowA = 1 - ε Σ_{j<n} C(N,j)/r^j
        if which == 'e': return (F(1), -F(sum(comb(N, j) for j in range(n))))
        return (F(1), F(0))
    rj = (F(1), F(0)) if which == 'e' else (F(1), F(1))
    a, b, c = [], [], []
    for n in range(N + 1):
        an = jdiv(jmul((F(N - n, N), F(0)), A(n)), A(n + 1))
        cn = jdiv(jmul(jmul(rj, (F(n, N), F(0))), A(n + 1)), A(n))
        a.append(an); c.append(cn); b.append(jsub(jsub((F(1), F(0)), an), cn))
    return a, b, c

def table(a, b, c):
    N = len(a) - 1
    Z = (F(0), F(0)); O = (F(1), F(0))
    prev = [[Z]*(N+1) for _ in range(N+1)]; cur = [[O if i == j else Z for j in range(N+1)] for i in range(N+1)]
    T = [cur]
    for m in range(N):
        nxt = []
        for i in range(N+1):
            row = []
            for j in range(N+1):
                v = jsub(jmul(jsub(b[i], b[m]), cur[i][j]), jmul(c[m], prev[i][j]))
                if i: v = jadd(v, jmul(c[i], cur[i-1][j]))
                if i < N: v = jadd(v, jmul(a[i], cur[i+1][j]))
                row.append(jdiv(v, a[m]))
            nxt.append(row)
        prev, cur = cur, nxt; T.append(cur)
    return T

def lam(N):
    Te = table(*lowK_jets(N, 'e')); Tr = table(*lowK_jets(N, 'r'))
    best = F(0); arg = None
    for m in range(N+1):
        for n in range(N+1):
            for k in range(N+1):
                if not (m <= n + k and n <= m + k and k <= m + n): continue
                if Te[m][n][k][0] != 0: continue
                A = Te[m][n][k][1]; B = -Tr[m][n][k][1]
                if A < 0:
                    assert B > 0, (m, n, k, B)
                    if -A / B > best: best, arg = -A / B, (m, n, k)
    return best, arg

if __name__ == '__main__':
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    for N in range(2, Nmax + 1):
        print(N, *lam(N), flush=True)
