"""lift.py variants with randomized rules: remove a uniform element of J, add a uniform element of J minus S;
and mixtures of the max/min rule with its mirror."""
import sys, itertools
from fractions import Fraction as F
import lift
from lift import check

def make_rule(kind):
    if kind == 'uniform':
        return ('uniform', None)
    return kind

def lift_matrix_mixed(N, sig, u, v, mode, lam=F(1, 2)):
    states = [frozenset(S) for k in range(N+1) for S in itertools.combinations(range(N), k)]
    idx = {S: i for i, S in enumerate(states)}
    D = [sum(F(sig[k-1])*len(list(itertools.combinations(range(n), k))) for k in range(1, n+1)) for n in range(N+1)]
    M = [[F(0)]*len(states) for _ in states]
    Js = [frozenset(J) for k in range(1, N+1) for J in itertools.combinations(range(N), k)]
    for S in states:
        for J in Js:
            w = F(sig[len(J)-1])/D[N]
            if w == 0: continue
            if J <= S:
                M[idx[S]][idx[S]] += u*w
                if mode == 'uniform':
                    for e in J: M[idx[S - {e}]][idx[S]] += v*w/len(J)
                else:
                    M[idx[S - {max(J)}]][idx[S]] += v*w*lam; M[idx[S - {min(J)}]][idx[S]] += v*w*(1 - lam)
            else:
                R = J - S
                if mode == 'uniform':
                    for e in R: M[idx[S | {e}]][idx[S]] += w/len(R)
                else:
                    M[idx[S | {min(R)}]][idx[S]] += w*lam; M[idx[S | {max(R)}]][idx[S]] += w*(1 - lam)
    return states, M, [x/D[N] for x in D]

for mode in ('uniform', 'mix'):
    lift.lift_matrix = (lambda N, sig, u, v, rule, mode=mode: lift_matrix_mixed(N, sig, u, v, mode))
    for N in (3, 4):
        for name, sig in (('Krawtchouk', [1] + [0]*(N-1)), ('geometric x=1', [1]*N), ('Q x=1', [1, 1] + [0]*(N-2)),
                          ('LC 1,1/2,1/8', [F(1)] + [F(1, 2)**(k*(k+1)//2) for k in range(1, N)])):
            res = [float(check(N, [F(x) for x in sig], r, None)) for r in (F(1, 3), F(1))]
            print(f'{mode:8s} N={N} {name:14s}: min entry {res}', flush=True)
