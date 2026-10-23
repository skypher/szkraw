"""Exact witnesses for the P3 Section 9 numeric claims formalized in lean/Szkraw/RuleCounterexamples.lean:
for each case a negative product coefficient g(m,n;k) (the corner g(N,N;N) when it is negative, else the first
negative entry in the order m, n, k), computed in exact rational arithmetic. Usage: p3_numeric_witnesses.py"""
from fractions import Fraction as F
import sys

def stoch(N, b, c):
    A = [F(1)] + [1 - b[n] - c[n] for n in range(1, N)] + [F(0)]
    B = [F(0)] + [b[n] for n in range(1, N)] + [1 - c[N]]
    C = [F(0)] + [c[n] for n in range(1, N + 1)]
    return A, B, C

def kraw_dir(N, r, eps, db, dc):
    b = [(1 - r) * n / N + eps * db(n) for n in range(N + 1)]
    c = [r * n / N + eps * dc(n) for n in range(N + 1)]
    return stoch(N, b, c)

def column(a, b, c, k):
    N = len(a) - 1
    prev = [F(0)] * (N + 1); cur = [F(int(i == k)) for i in range(N + 1)]
    cols = [cur]
    for m in range(N):
        nxt = []
        for i in range(N + 1):
            v = (b[i] - b[m]) * cur[i] - c[m] * prev[i]
            if i: v += c[i] * cur[i - 1]
            if i < N: v += a[i] * cur[i + 1]
            nxt.append(v / a[m])
        prev, cur = cur, nxt; cols.append(cur)
    return cols

def witness(a, b, c):
    N = len(a) - 1
    if column(a, b, c, N)[N][N] < 0: return (N, N, N)
    best = None
    for k in range(N + 1):
        cols = column(a, b, c, k)
        for m in range(N + 1):
            for n in range(N + 1):
                if cols[m][n] < 0 and (best is None or (m, n, k) < best): best = (m, n, k)
    return best

if __name__ == '__main__':
    for r, eps, Ns in ((F(4, 5), F(1, 100), range(6, 15)), (F(19, 20), F(1, 1000), range(4, 15))):
        for N in Ns:
            a, b, c = kraw_dir(N, r, eps, lambda n: 1, lambda n: 0)
            print(f'rule beta=1 gamma=0 r={r} eps={eps} N={N}: witness {witness(a, b, c)}', flush=True)
    for N, r, e in ((120, F(1, 2), F(-63, 10**7)), (100, F(2, 5), F(-32, 10**4)), (120, F(1, 3), F(-16, 10**3))):
        a, b, c = kraw_dir(N, r, e, lambda n: 0, lambda n: int(n == N))
        g = column(a, b, c, N)[N][N]
        print(f'terminal r={r} N={N} e={e}: g(N,N;N) < 0: {g < 0}', flush=True)
