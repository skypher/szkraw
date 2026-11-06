"""Finite classical families normalized as in P1/P2 (row sums one, R_i(1)=1).

Each family gives exact values p_n(X_x) on its grid x=0..N from the
(basic) hypergeometric definition in Koekoek-Lesky-Swarttouw, with
p_n(X_0)=1.  The three-term recurrence is fitted on the grid and verified
at every grid point, so a wrong formula is detected rather than used.
"""
from fractions import Fraction as F


def poch(a, k):
    p = F(1)
    for j in range(k):
        p *= a + j
    return p


def qpoch(a, q, k):
    p = F(1)
    for j in range(k):
        p *= 1 - a * q**j
    return p


def hyp(num, den, z, kmax):
    s, t = F(0), F(1)
    for k in range(kmax + 1):
        s += t
        if k == kmax:
            break
        for a in num:
            t *= a + k
        for b in den:
            t /= b + k
        t *= z
        t /= k + 1
    return s


def qhyp(num, den, q, z, kmax):
    s = F(0)
    for k in range(kmax + 1):
        t = F(1)
        for a in num:
            t *= qpoch(a, q, k)
        for b in den:
            t /= qpoch(b, q, k)
        s += t * z**k / qpoch(q, q, k)
    return s


def hahn(N, al, be):
    X = [F(x) for x in range(N + 1)]
    P = [[hyp([-n, n + al + be + 1, -x], [al + 1, -N], 1, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def dual_hahn(N, ga, de):
    X = [F(x * (x + ga + de + 1)) for x in range(N + 1)]
    P = [[hyp([-n, -x, x + ga + de + 1], [ga + 1, -N], 1, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def racah(N, be, ga, de):
    al = F(-N - 1)
    X = [F(x * (x + ga + de + 1)) for x in range(N + 1)]
    P = [[hyp([-n, n + al + be + 1, -x, x + ga + de + 1], [al + 1, be + de + 1, ga + 1], 1, min(n, x))
          for x in range(N + 1)] for n in range(N + 1)]
    return X, P


def krawtchouk(N, p):
    X = [F(x) for x in range(N + 1)]
    P = [[hyp([-n, -x], [-N], 1 / F(p), min(n, x)) for x in range(N + 1)] for n in range(N + 1)]
    return X, P


def q_krawtchouk(N, p, q):
    X = [q**-x for x in range(N + 1)]
    P = [[qhyp([q**-n, q**-x, -p * q**n], [q**-N, 0], q, q, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def quantum_q_krawtchouk(N, p, q):
    X = [q**-x for x in range(N + 1)]
    P = [[qhyp([q**-n, q**-x, 0], [q**-N, p * q], q, q, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def affine_q_krawtchouk(N, p, q):
    X = [q**-x for x in range(N + 1)]
    P = [[qhyp([q**-n, 0, q**-x], [p * q, q**-N], q, q, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def dual_q_krawtchouk(N, c, q):
    X = [q**-x + c * q**(x - N) for x in range(N + 1)]
    P = [[qhyp([q**-n, q**-x, c * q**(x - N)], [q**-N, 0], q, q, min(n, x)) for x in range(N + 1)]
         for n in range(N + 1)]
    return X, P


def q_hahn(N, al, be, q):
    X = [q**-x for x in range(N + 1)]
    P = [[qhyp([q**-n, al * be * q**(n + 1), q**-x], [al * q, q**-N], q, q, min(n, x))
          for x in range(N + 1)] for n in range(N + 1)]
    return X, P


def dual_q_hahn(N, ga, de, q):
    X = [q**-x + ga * de * q**(x + 1) for x in range(N + 1)]
    P = [[qhyp([q**-n, q**-x, ga * de * q**(x + 1)], [ga * q, q**-N], q, q, min(n, x))
          for x in range(N + 1)] for n in range(N + 1)]
    return X, P


def solve(M, y):
    """Exact least squares via normal equations; returns solution."""
    k = len(M[0])
    A = [[sum(M[r][i] * M[r][j] for r in range(len(M))) for j in range(k)] for i in range(k)]
    b = [sum(M[r][i] * y[r] for r in range(len(M))) for i in range(k)]
    for c in range(k):
        piv = next(r for r in range(c, k) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        b[c], b[piv] = b[piv], b[c]
        for r in range(k):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [A[r][j] - f * A[c][j] for j in range(k)]
                b[r] -= f * b[c]
    return [b[i] / A[i][i] for i in range(k)]


def recurrence(X, P):
    """Fit X p_n = A_n p_{n+1} + B_n p_n + C_n p_{n-1} on the grid; verify exactly."""
    N = len(X) - 1
    A, B, C = [], [], []
    for n in range(N + 1):
        cols = []
        if n < N:
            cols.append([P[n + 1][x] for x in range(N + 1)])
        cols.append([P[n][x] for x in range(N + 1)])
        if n > 0:
            cols.append([P[n - 1][x] for x in range(N + 1)])
        M = [[col[x] for col in cols] for x in range(N + 1)]
        y = [X[x] * P[n][x] for x in range(N + 1)]
        z = solve(M, y)
        for x in range(N + 1):
            if sum(M[x][i] * z[i] for i in range(len(z))) != y[x]:
                raise ValueError(f"no three-term recurrence at n={n}")
        z = list(z)
        A.append(z.pop(0) if n < N else F(0))
        B.append(z.pop(0))
        C.append(z.pop(0) if n > 0 else F(0))
    return A, B, C


def normalize(X, P, e):
    """Array (a,b,c) normalized at grid endpoint e (0 or N), or None."""
    N = len(X) - 1
    if X[e] != max(X) and X[e] != min(X):
        return None
    A, B, C = recurrence(X, P)
    pe = [P[n][e] for n in range(N + 1)]
    if any(v == 0 for v in pe):
        return None
    s = X[e] - B[0]
    a = [(A[n] * pe[n + 1] / pe[n] if n < N else F(0)) / s for n in range(N + 1)]
    b = [(B[n] - B[0]) / s for n in range(N + 1)]
    c = [(C[n] * pe[n - 1] / pe[n] if n > 0 else F(0)) / s for n in range(N + 1)]
    assert a[0] == 1 and b[0] == 0 and all(a[n] + b[n] + c[n] == 1 for n in range(N + 1))
    if not (all(a[n] > 0 for n in range(N)) and all(c[n] > 0 for n in range(1, N + 1))):
        return None
    return a, b, c
