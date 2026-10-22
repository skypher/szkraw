"""Terminal column at t = 0 (r = 1, b = 0) in monic form: x q_i = q_{i+1} + phi_i q_{i-1}, q_{N+1} = 0 on the support.
Dmon(m) = phi_N [x^N](q_m q_{N-1} mod q_{N+1}) - phi_m [x^N](q_{m-1} q_N mod q_{N+1})   (coefficient of q_N).
Compute symbolically in phi_1..phi_N and check that it depends only on the end values (N-independence)."""
import sys
import sympy as sp
def dmon(N, m):
    x = sp.Symbol('x'); ph = sp.symbols(f'p1:{N+1}')
    q = [sp.Integer(1), x]
    for i in range(1, N+1): q.append(sp.expand(x*q[i] - ph[i-1]*q[i-1]))
    Q = sp.Poly(q[N+1], x)
    def topcoef(e):
        r = sp.Poly(sp.expand(e), x).rem(Q)
        return r.coeff_monomial(x**N)
    return sp.factor(sp.expand(ph[N-1]*topcoef(q[m]*q[N-1]) - ph[m-1]*topcoef(q[m-1]*q[N]))), ph
for m in (3, 5):
    for N in (2*m, 2*m + 1, 2*m + 2):
        e, ph = dmon(N, m)
        # rename end variables: phi_{N-j} -> e_j
        sub = {ph[N-1-j]: sp.Symbol(f'E{j}') for j in range(m)}
        print(f'm={m} N={N}:', sp.factor(e.subs(sub)), flush=True)
