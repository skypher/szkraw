# Verify: closed-form certificate Z, the commutator identity, and Lemma 9.2 against a dual-number derivative.
from fractions import Fraction as F
from math import comb
import random, sys

def Zc(N, m, n):
    if (m + n) % 2 == 0: return F(0)
    e = (n - m + 1) // 2          # floor division matches integer exponent (d+1)/2 for odd d
    sign = -1 if e % 2 else 1
    return F(comb(N, n) * sign, 2 * comb(N - 1, (m + n - 1) // 2))

def check_comm(N):
    J = [[F(0)]*(N+1) for _ in range(N+1)]
    for i in range(N+1):
        if i < N: J[i][i+1] = F(N-i, N)
        if i > 0: J[i][i-1] = F(i, N)
    Z = [[Zc(N, m, n) for n in range(N+1)] for m in range(N+1)]
    for m in range(N+1):
        for n in range(1, N+1):
            zj = sum(Z[m][k]*J[k][n] for k in range(N+1))
            jz = sum(J[m][k]*Z[k][n] for k in range(N+1))
            want = 1 if (m == N and n == N) else 0
            if zj - jz != want: return False
    return True

class D:  # dual numbers x + y*eps
    def __init__(s, x, y=F(0)): s.x, s.y = F(x), F(y)
    def __add__(s, o): o = o if isinstance(o, D) else D(o); return D(s.x+o.x, s.y+o.y)
    __radd__ = __add__
    def __sub__(s, o): o = o if isinstance(o, D) else D(o); return D(s.x-o.x, s.y-o.y)
    def __rsub__(s, o): return D(o) - s
    def __mul__(s, o): o = o if isinstance(o, D) else D(o); return D(s.x*o.x, s.x*o.y+s.y*o.x)
    __rmul__ = __mul__
    def inv(s): return D(1/s.x, -s.y/(s.x*s.x))

def corner_deriv(N, db, dc):
    # stochArray coordinates at K_{N,1} + eps*(db, dc)
    b = [D(F(0))] + [D(F(0), db[n]) for n in range(1, N)] + [None]
    c = [D(F(0))] + [D(F(n, N), dc[n]) for n in range(1, N+1)]
    b[N] = 1 - c[N]
    a = [D(1)] + [1 - b[n] - c[n] for n in range(1, N)] + [D(0)]
    J = [[D(0)]*(N+1) for _ in range(N+1)]
    for i in range(N+1):
        if i < N: J[i][i+1] = a[i]
        J[i][i] = b[i]
        if i > 0: J[i][i-1] = c[i]
    I = [[D(1) if i == j else D(0) for j in range(N+1)] for i in range(N+1)]
    Zm = [[D(0)]*(N+1) for _ in range(N+1)]
    prev, cur = Zm, I
    mm = lambda A, B: [[sum((A[i][k]*B[k][j] for k in range(N+1)), D(0)) for j in range(N+1)] for i in range(N+1)]
    for n in range(N):
        JB = mm(J, cur)
        nxt = [[a[n].inv() * (JB[i][j] - b[n]*cur[i][j] - c[n]*prev[i][j]) for j in range(N+1)] for i in range(N+1)]
        prev, cur = cur, nxt
    return cur[N][N].x, cur[N][N].y

def lemma_value(N, db, dc):
    h = N // 2
    sN = F((-1)**(h + 1), comb(N - 1, (N - 1) // 2))
    tot = F(0)
    for n in range(N + 1):
        dbn = F(0) if n == 0 else (-dc[N] if n == N else db[n])
        dcn = F(0) if n == 0 else dc[n]
        Fn = dbn + 2*dcn if N % 2 == 0 else dbn
        tot += (-1)**n * comb(N, n) * Fn
    return sN * tot

random.seed(1)
for N in range(2, int(sys.argv[1]) + 1):
    ok = check_comm(N)
    db = [F(0)] + [F(random.randint(-9, 9), random.randint(1, 5)) for _ in range(1, N)] + [F(0)]
    dc = [F(0)] + [F(random.randint(-9, 9), random.randint(1, 5)) for _ in range(1, N+1)]
    g0, d = corner_deriv(N, db, dc)
    print(N, "comm", ok, "g0", g0, "deriv", d, "lemma", lemma_value(N, db, dc), d == lemma_value(N, db, dc))
