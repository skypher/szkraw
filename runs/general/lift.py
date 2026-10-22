"""Positive-lift experiment. State space: subsets S of [N]. Lift X (times D_N): pick nonempty J with weight sigma_|J|;
  J subset of S: weight u -> stay at S; weight v -> S minus rem(J)   (interaction)
  else:          S plus add(J, S)                                   (up move)
rem/add rules are variants. Lumping: from |S| = n the up weight is D_N - D_n and the interaction weight is D_n, so X lumps to
the constant-ratio chain with profile d = D/D_N. Test: P_m(X) (three-term recurrence of the lumped chain) entrywise >= 0,
at sample (u, v) = (1-r, r). Exact rationals."""
import sys, itertools, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from corner_bern_num import profile

RULES = {
    'rem=min,add=min': (lambda J, S: min(J), lambda J, S: min(J - S)),
    'rem=max,add=min': (lambda J, S: max(J), lambda J, S: min(J - S)),
    'rem=min,add=max': (lambda J, S: min(J), lambda J, S: max(J - S)),
    'rem=max,add=max': (lambda J, S: max(J), lambda J, S: max(J - S)),
}

def lift_matrix(N, sig, u, v, rule):
    rem, add = RULES[rule]
    states = [frozenset(S) for k in range(N+1) for S in itertools.combinations(range(N), k)]
    idx = {S: i for i, S in enumerate(states)}
    D = [sum(F(sig[k-1])*len(list(itertools.combinations(range(n), k))) for k in range(1, n+1)) for n in range(N+1)]
    M = [[F(0)]*len(states) for _ in states]          # column convention: X e_S = sum_T M[T][S] e_T
    Js = [frozenset(J) for k in range(1, N+1) for J in itertools.combinations(range(N), k)]
    for S in states:
        for J in Js:
            w = F(sig[len(J)-1])/D[N]
            if w == 0: continue
            if J <= S:
                M[idx[S]][idx[S]] += u*w
                M[idx[S - {rem(J, S)}]][idx[S]] += v*w
            else:
                M[idx[S | {add(J, S)}]][idx[S]] += w
    return states, M, [x/D[N] for x in D]

def matmul(A, B):
    n = len(A); m = len(B[0]); K = len(B)
    return [[sum(A[i][k]*B[k][j] for k in range(K) if A[i][k] and B[k][j]) for j in range(m)] for i in range(n)]

def check(N, sig, r, rule):
    u, v = 1 - r, r
    states, X, d = lift_matrix(N, sig, u, v, rule)
    n = len(states); I = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    a = [1 - x for x in d]
    P = [I, X]; worst = F(0)
    for m in range(1, N):
        # x P_m = a_m P_{m+1} + u d_m P_m + v d_m P_{m-1}
        XP = matmul(X, P[m])
        Pn = [[(XP[i][j] - u*d[m]*P[m][i][j] - v*d[m]*P[m-1][i][j])/a[m] for j in range(n)] for i in range(n)]
        P.append(Pn)
    for m in range(N+1):
        mn = min(min(row) for row in P[m])
        worst = min(worst, mn)
    return worst

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    profs = {'Krawtchouk': [1] + [0]*(N-1), 'geometric x=1': [1]*N, 'Q x=1 (K=2)': [1, 1] + [0]*(N-2),
             'LC 1,1/2,1/8..': [F(1)] + [F(1, 2)**(k*(k+1)//2) for k in range(1, N)], 'log-convex 1,1/2,1/2..': [F(1)] + [F(1, 2)]*(N-1)}
    for name, sig in profs.items():
        for rule in RULES:
            res = [check(N, [F(x) for x in sig], r, rule) for r in (F(1, 3), F(1))]
            print(f'N={N} {name:24s} {rule:16s}: min entry of P_m(X) at r=1/3, 1: {[float(x) for x in res]}', flush=True)
