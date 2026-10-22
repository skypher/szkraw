"""Does the symmetric kernel K_k(S, Z) factor as (S + t Z)^k G_k(S, Z) for non-Krawtchouk profiles? (For Krawtchouk,
K_k = (1 + Z)^(N-k) (S + t Z)^k up to a constant.) Exact, via the true L tables."""
import sys
from fractions import Fraction as F
from math import comb
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/ql_proof')
from gamma_check import tables
S, Z, t = sp.symbols('S Z t')
def kernel(sig, N, k):
    D = [sum(comb(i, j)*sig[j-1] for j in range(1, min(i, len(sig)) + 1)) for i in range(N+1)]; T = D[N]
    d = [x/T for x in D]; H, _ = tables(d)
    A = [F(1)]
    for j in range(1, N+1): A.append(A[-1]*D[j])
    Q = [F(1)]
    for j in range(N): Q.append(Q[-1]*(T - D[j]))
    e = [Q[r]/A[r] for r in range(N+1)]
    z, w = sp.symbols('z w')
    Kzw = sum(sp.Rational(str(c))*e[m]*e[n]/e[k]*t**i*z**m*w**n for m in range(N+1) for n in range(N+1) for i, c in enumerate(H[m][n][k]))
    # convert to S, Z
    p = sp.Poly(sp.expand(Kzw), z, w); res = 0
    while not p.is_zero:
        (i, j), c = max(p.terms(), key=lambda mm: (mm[0][0], mm[0][1]))
        res += c*S**(i - j)*Z**j; p = p - sp.Poly(sp.expand(c*(z + w)**(i - j)*(z*w)**j), z, w)
    return sp.expand(res)
for name, sig, N in (('Krawtchouk', [F(1)], 4), ('quadratic x=1', [F(1), F(1)], 4), ('cubic', [F(1), F(1), F(1, 2)], 4), ('geometric q=2', [F(1)]*5, 5)):
    for k in range(0, N+1):
        K = kernel(sig, N, k)
        q, rem = sp.div(sp.Poly(K, S, Z, t), sp.Poly((S + t*Z)**k, S, Z, t))
        print(f'{name} N={N} k={k}: divisible by (S + tZ)^k: {rem.is_zero}' + (f'; quotient {sp.factor(q.as_expr())}' if rem.is_zero and k <= 1 else ''), flush=True)
