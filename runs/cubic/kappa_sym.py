"""Cubic weighted B-detour D(l,n) = K phi_2(l) phi_n(l+1) - L c_{l+1} phi_{n+2}(l), K = (n+1)(n+2), L = 8(n-1),
polarized in the ratio basis e_0 = 1, e_1 = x, e_2 = C(x,2), e_3 = C(x,3) (rho = r e_0 + t e_1 + tau e_2 + sigma e_3).
Leibniz: phi_m[e_b](l) = sum_i C(m,i) C(l+m-i, b-i) u_{m-i}, u_k = f_k(l), f_k(l+1) = u_k + u_{k+1}.
kappa(al, be) is bilinear: small block u_a (a = 0,1,2) times n-block u_{n+j} (j = -3..2); returned as
{(a, j): polynomial in (l, n)} (symbolic l, n). Valid when the blocks do not overlap (n >= 6)."""
import sympy as sp
l, n = sp.symbols('l n', nonnegative=True)
def C(x, k): return sp.expand(sp.expand_func(sp.binomial(x, k))) if k >= 0 else 0
def small_phi2(al):
    return {2 - i: C(2, i) * C(l + 2 - i, al - i) for i in range(0, min(al, 2) + 1)}
def small_c(al):
    return {0: C(l + 1, al), 1: C(l + 1, al)}
def blk_phin1(be):
    out = {}
    for i in range(0, be + 1):
        cf = C(n, i) * C(l + 1 + n - i, be - i)
        for j in (-i, -i + 1): out[j] = out.get(j, 0) + cf
    return out
def blk_phin2(be):
    return {2 - i: C(n + 2, i) * C(l + n + 2 - i, be - i) for i in range(0, be + 1)}
K, L = (n + 1) * (n + 2), 8 * (n - 1)
def _prod(S, B, w, acc):
    for a, x in S.items():
        for j, y in B.items():
            acc[(a, j)] = acc.get((a, j), 0) + w * x * y
def kappa(al, be):
    acc = {}
    pairs = [(al, be)] if al == be else [(al, be), (be, al)]
    for x, y in pairs:
        _prod(small_phi2(x), blk_phin1(y), K, acc)
        _prod(small_c(x), blk_phin2(y), -L, acc)
    return {k: sp.expand(v) for k, v in acc.items() if sp.expand(v) != 0}
NAMES = {'rt': (0, 1), 'tt': (1, 1), 'ts': (1, 3), 'taus': (2, 3), 'ss': (3, 3), 'ttau': (1, 2), 'rs': (0, 3),
         'rr': (0, 0), 'rtau': (0, 2), 'tautau': (2, 2)}
def kap(name):
    if '+' in name:
        out = {}
        for part in name.split('+'):
            for k, v in kap(part).items(): out[k] = sp.expand(out.get(k, 0) + v)
        return out
    return kappa(*NAMES[name])
if __name__ == '__main__':
    # cross-check against the u-form of cubic_quadB_abel.py at numeric (l, n), n >= 6
    import sys, os
    from fractions import Fraction as Fr
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from small_n_forms import _g, MON
    bad = 0
    for lv in range(0, 4):
        for nv in range(6, 9):
            U = _g['form'](lv, nv)
            for name in ('rt', 'tt', 'ts', 'taus', 'ss', 'ttau', 'rs', 'rr', 'rtau', 'tautau'):
                ref = {}
                for (a, b), v in U.items():
                    P = sp.Poly(sp.expand(sp.expand_func(v)), *[_g[s] for s in ('r', 't', 'tau', 'sig')])
                    cf = P.coeff_monomial(MON[name])
                    if cf != 0: ref[(a, b - nv)] = ref.get((a, b - nv), 0) + cf
                mine = {k: v.subs({l: lv, n: nv}) for k, v in kap(name).items()}
                keys = set(ref) | set(mine)
                if any(sp.simplify(ref.get(k, 0) - mine.get(k, 0)) != 0 for k in keys): bad += 1; print('mismatch', lv, nv, name)
    print('cross-check mismatches:', bad)
