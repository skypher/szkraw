"""Cubic weighted B-detour, small n (2, 3): the scalar coefficient forms k_ts, k_ttau, k_rs as quadratic forms in
u_k = f_k(l) (shifted Newton coefficients of the profile at l), coefficients polynomial in l. Helper: forms(n) returns
{name: sympy expr in (l, u0..u7)}; lam(n) returns numeric callables f(l, u)."""
import os, sys
import sympy as sp
_HERE = os.path.dirname(os.path.abspath(__file__))
_VR = os.path.join(_HERE, '..', 'varratio')
_src = open(os.path.join(_VR, 'cubic_quadB_abel.py')).read().split('fails = []; cnt = 0')[0]
_src = _src.replace('lmax, nmax = int(sys.argv[1]), int(sys.argv[2])', '')
_g = {}
exec(_src, _g)
r, t, tau, sig = _g['r'], _g['t'], _g['tau'], _g['sig']
l = sp.Symbol('l', nonnegative=True)
u = sp.symbols('u0:8', nonnegative=True)
MON = {'rt': r * t, 'tt': t ** 2, 'ts': t * sig, 'taus': tau * sig, 'ss': sig ** 2, 'ttau': t * tau, 'rs': r * sig,
       'rr': r ** 2, 'rtau': r * tau, 'tautau': tau ** 2}
_cache = {}
def forms(n):
    if n in _cache: return _cache[n]
    U = _g['form'](l, n); out = {k: 0 for k in MON}
    for (a, b), v in U.items():
        P = sp.Poly(sp.expand(sp.expand_func(v)), r, t, tau, sig)
        for k, m in MON.items():
            out[k] += sp.expand(P.coeff_monomial(m)) * u[a] * u[b]
    out = {k: sp.expand(v) for k, v in out.items()}
    _cache[n] = out
    return out
def lam(n):
    F = forms(n)
    return {k: sp.lambdify((l, u), v, 'math') for k, v in F.items()}
