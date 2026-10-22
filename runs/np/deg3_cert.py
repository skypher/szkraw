"""Forced certificate for degree-3 (NP): Q = sum lam_ij D(i,j) + sum mu_ij x_i x_j with
lam11 = -[x0x2], lam12 = -[x0x3], lam13 = -[x0x4], lam23 = -[x1x4], lam33 = -[x2x4], lam22 = lam13 - [x1x3];
then mu = residual coefficients. Prints all multipliers factored."""
import sympy as sp
import sys
sys.path.insert(0, '/home/yang/szkraw/runs/np')
from deg3_sym import Q, x, n1, n2, n3, k
c = lambda i, j: Q.coeff_monomial(x[i] * x[j])
lam = {(1, 1): -c(0, 2), (1, 2): -c(0, 3), (1, 3): -c(0, 4), (2, 3): -c(1, 4), (3, 3): -c(2, 4)}
lam[(2, 2)] = lam[(1, 3)] - c(1, 3)
mu = {(1, 1): c(1, 1) - lam[(1, 1)], (1, 2): c(1, 2) - lam[(1, 2)], (1, 3): c(1, 3) - lam[(1, 3)] + lam[(2, 2)],
      (2, 2): c(2, 2) - lam[(2, 2)], (2, 3): c(2, 3) - lam[(2, 3)], (3, 3): c(3, 3) - lam[(3, 3)]}
if __name__ == '__main__':
    for kk, v in lam.items(): print('lam', kk, sp.factor(v))
    for kk, v in mu.items(): print('mu ', kk, sp.factor(v))
    D = lambda i, j: x[i] * x[j] - x[i - 1] * x[j + 1]
    recon = sum(v * D(*kk) for kk, v in lam.items()) + sum(v * x[a] * x[b] for (a, b), v in mu.items())
    print('identity exact:', sp.expand(recon - Q.as_expr()) == 0)
