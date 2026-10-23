"""Numerical search for the extremal configuration of the cubic weighted B-detour ratio
K phi2(l) phi_n(l+1) / (L c_{l+1} phi_{n+2}(l)) over LC sequences u (u_1 = 1, u_0 = z <= min(l, 1/q), ratios
q = y_1 >= y_2 >= ... >= 0) and cubic ratios with r sigma <= t tau. Float, Nelder-Mead from random starts.
Prints the best ratio and its configuration (ratios y_k, z, and r,t,tau,sigma). Usage: cubic_quadB_extremal.py l n starts seed"""
import sys, math, random
import numpy as np
from scipy.optimize import minimize
l, n, starts, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = np.random.default_rng(seed)
M = n + 6
def unpack(x):
    x = np.clip(x, -25, 25)
    # x: log q, increments of -log ratio (>=0 via softplus), z fraction, ratio params
    sp = lambda v: np.log1p(np.exp(v))
    q = math.exp(x[0])
    dec = [sp(v) for v in x[1:M]]
    ys = [q]
    for dv in dec[:M - 2]: ys.append(ys[-1] * math.exp(-dv))
    u = [0.0, 1.0]
    for y in ys[:M - 1]: u.append(u[-1] * y)
    zmax = min(l, 1 / q) if l > 0 else 0.0
    z = zmax / (1 + math.exp(-x[M])) if zmax > 0 else 0.0
    u[0] = z
    r, t, tau = (math.exp(v) for v in x[M + 1:M + 4])
    sig_max = t * tau / max(r, 1e-300)
    sig = sig_max / (1 + math.exp(-x[M + 4]))
    return u, (r, t, tau, sig), ys
def D_ratio(x):
    u, (r, t, tau, sig), _ = unpack(x)
    rho = lambda xx: r + t * xx + tau * math.comb(xx, 2) + sig * math.comb(xx, 3)
    N = l + n + 2
    d = [sum(math.comb(i - l, m) * u[m] for m in range(i - l + 1)) if i >= l else None for i in range(N + 1)]
    # values from base l: d_{l+i} = sum_m C(i,m) u_m
    dv = lambda i: sum(math.comb(i, m) * u[m] for m in range(i + 1))
    c = lambda i: rho(l + i) * dv(i)
    Dn = lambda k, base: sum((-1) ** (k - j) * math.comb(k, j) * c(base + j) for j in range(k + 1))
    K, L = (n + 1) * (n + 2), 8 * (n - 1)
    num = K * Dn(2, 0) * Dn(n, 1); den = L * c(1) * Dn(n + 2, 0)
    return num / den if den > 1e-300 else 1e9
best = None
for s in range(starts):
    x0 = np.concatenate([[rng.normal(0, 3)], rng.normal(0, 2, M - 1), [rng.normal(0, 2)], rng.normal(0, 4, 3), [rng.normal(0, 2)]])
    res = minimize(D_ratio, x0, method='Nelder-Mead', options={'maxiter': 20000, 'xatol': 1e-10, 'fatol': 1e-12})
    if best is None or res.fun < best[0]: best = (res.fun, res.x)
u, ratio, ys = unpack(best[1])
print(f'(l,n)=({l},{n}): min ratio {best[0]:.6f}')
print('  ratios y_k:', [round(y, 4) for y in ys[:n + 4]])
print('  z=u0:', round(u[0], 5), ' z/min(l,1/q):', round(u[0] / min(l, 1 / ys[0]), 4) if l > 0 else 0)
print('  r,t,tau,sigma:', [f'{v:.3g}' for v in ratio], ' r*sig/(t*tau):', round(ratio[0] * ratio[3] / (ratio[1] * ratio[2]), 4))
