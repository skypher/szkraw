"""Brute force over all deterministic remove/add rules of the subset lift (lift.py) at N = 3 for a given sigma;
report rules with P_m(X) entrywise >= 0 at r = 1/3 and r = 1 (then confirm at more r)."""
import sys, itertools
from fractions import Fraction as F
N = 3
sig = [F(x) for x in sys.argv[1].split(',')]
states = [frozenset(S) for k in range(N+1) for S in itertools.combinations(range(N), k)]
idx = {S: i for i, S in enumerate(states)}
D = [sum(sig[k-1]*len(list(itertools.combinations(range(n), k))) for k in range(1, n+1)) for n in range(N+1)]
d = [x/D[N] for x in D]; a = [1 - x for x in d]
Js = [frozenset(J) for k in range(1, N+1) for J in itertools.combinations(range(N), k) if sig[k-1] != 0]
choices = []      # (kind, J, S, options)
for S in states:
    for J in Js:
        if J <= S:
            if len(J) > 1: choices.append(('rem', J, S, sorted(J)))
        else:
            R = J - S
            if len(R) > 1: choices.append(('add', J, S, sorted(R)))
def build(sel, u, v):
    M = [[F(0)]*len(states) for _ in states]
    ch = {(k, J, S): o for (k, J, S, _), o in zip(choices, sel)}
    for S in states:
        for J in Js:
            w = sig[len(J)-1]/D[N]
            if J <= S:
                M[idx[S]][idx[S]] += u*w
                e = ch.get(('rem', J, S), min(J)); M[idx[S - {e}]][idx[S]] += v*w
            else:
                R = J - S; e = ch.get(('add', J, S), min(R)); M[idx[S | {e}]][idx[S]] += w
    return M
def mm(A, B):
    n = len(A); return [[sum(A[i][k]*B[k][j] for k in range(n) if A[i][k] and B[k][j]) for j in range(n)] for i in range(n)]
def ok(sel, r):
    u, v = 1 - r, r; X = build(sel, u, v); n = len(states)
    I = [[F(int(i == j)) for j in range(n)] for i in range(n)]; P = [I, X]
    for m in range(1, N):
        XP = mm(X, P[m]); P.append([[(XP[i][j] - u*d[m]*P[m][i][j] - v*d[m]*P[m-1][i][j])/a[m] for j in range(n)] for i in range(n)])
    return all(x >= 0 for Pm in P for row in Pm for x in row)
good = []
for sel in itertools.product(*[c[3] for c in choices]):
    if ok(sel, F(1)) and ok(sel, F(1, 3)) and ok(sel, F(2, 3)) and ok(sel, F(1, 10)): good.append(sel)
print(f'sigma={[str(x) for x in sig]}: {len(choices)} binary choices, {2**len(choices) if all(len(c[3]) == 2 for c in choices) else "?"} rules, {len(good)} positive at r = 1, 1/3, 2/3, 1/10')
