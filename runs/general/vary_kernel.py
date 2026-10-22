"""Non-constant ratio: h-transform any array to a'' = 1 - d'', c'' = d'', b'' = b/s (lambda = Perron eigenvector of the
zero-diagonal matrix with M[i,i+1] = a_i, M[i,i-1] = c_i, eigenvalue s), then recover the symmetric kernel coefficients
omega_{l,a} (K_k = sum omega S^a Z^l in the E-basis E_i = e_i p_i, e_{i+1}/e_i = a''_i/d''_{i+1}) from the exact
linearization coefficients, and report min omega (scaled) and the Newton coefficients of d'' and b''.
Family L: increments 1 + tt*i/N (profile), ratio rho_n = r + kappa*n/N."""
import sys
from fractions import Fraction as F
from math import comb
import mpmath as mp
sys.path.insert(0, '/home/yang/szkraw')
from probe import linearization, first_negative
mp.mp.dps = 50
def L_family(N, r, kappa, tt):
    inc = [1 + tt*F(i, N) for i in range(1, N+1)]; S = sum(inc); d = [F(0)]
    for x in inc: d.append(d[-1] + x/S)
    rho = [r + kappa*F(n, N) for n in range(N+1)]
    c = [rho[n]*d[n] for n in range(N+1)]; b = [d[n] - c[n] for n in range(N+1)]; a = [1 - x for x in d]
    return a, b, c
def analyse(a, b, c):
    N = len(a) - 1
    M = mp.matrix(N+1, N+1)
    for i in range(N+1):
        if i < N: M[i, i+1] = mp.mpf(a[i].numerator)/a[i].denominator
        if i > 0: M[i, i-1] = mp.mpf(c[i].numerator)/c[i].denominator
    E, ER = mp.eig(M)
    idx = max(range(N+1), key=lambda i: mp.re(E[i])); s = mp.re(E[idx])
    lam = [mp.re(ER[i, idx]) for i in range(N+1)]
    if lam[0] < 0: lam = [-x for x in lam]
    fl = lambda q: mp.mpf(q.numerator)/q.denominator
    d2 = [fl(c[i])*(lam[i-1] if i else 0)/(s*lam[i]) for i in range(N+1)]
    a2 = [fl(a[i])*(lam[i+1] if i < N else 0)/(s*lam[i]) for i in range(N+1)]
    b2 = [fl(b[i])/s for i in range(N+1)]
    nu = [sum((-1)**(k-i)*comb(k, i)*d2[i] for i in range(k+1)) for k in range(1, N+1)]
    be = [sum((-1)**(k-i)*comb(k, i)*b2[i] for i in range(k+1)) for k in range(0, N+1)]
    # exact linearization of the original array, converted: R_i = lam_i' p_i with lam' normalized lam_i/lam_0 * s^i ...
    g = linearization(a, b, c)
    # R_i(x) = mu_i p_i(x/s) with mu_i = prod_{j<i} (s a''_j / a_j)^{-1}...: use p-recurrence coefficients directly:
    # x R_i = a_i R_{i+1} + ...;  y p_i = a2_i p_{i+1} + b2_i p_i + d2_i p_{i-1} with x = s y  =>  R_i = mu_i p_i, mu_{i+1}/mu_i = s a2_i / a_i
    mu = [mp.mpf(1)]
    for i in range(N): mu.append(mu[-1]*s*a2[i]/fl(a[i]))
    e = [mp.mpf(1)]
    for i in range(N): e.append(e[-1]*a2[i]/d2[i+1])
    worst = mp.inf
    for k in range(N+1):
        Lm = lambda m, n: fl(g[m][n][k])*mu[k]/(mu[m]*mu[n])*e[m]*e[n]/e[k]     # H = g mu_k/(mu_m mu_n); L = H e_m e_n / e_k
        om = {}
        for m in range(N+1):
            for n in range(m, N+1):
                rest = Lm(m, n) - sum(om.get((l, m+n-2*l), 0)*comb(m+n-2*l, m-l) for l in range(m))
                om[(m, n-m)] = rest
        scale = max(abs(v) for v in om.values())
        worst = min(worst, min(v/scale for v in om.values()))
    return s, [mp.nstr(x, 4) for x in nu], [mp.nstr(x, 4) for x in be], worst, first_negative(g)
if __name__ == '__main__':
    for N in (4, 6, 8):
        for r, kappa, tt in ((F(1, 5), F(2, 5), F(0)), (F(1, 5), F(2, 5), F(1)), (F(1, 2), F(1, 4), F(1)), (F(1, 10), F(9, 20), F(3))):
            a, b, c = L_family(N, r, kappa, tt)
            s, nu, be, worst, fn = analyse(a, b, c)
            print(f'N={N} r={r} kappa={kappa} t={tt}: (P) {"fails "+str(fn[:3]) if fn else "holds"}; min omega/scale {mp.nstr(worst, 4)}; '
                  f'nu(d\'\')={nu[:4]}; beta(b\'\')={be[:4]}', flush=True)
