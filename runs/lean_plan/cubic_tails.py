"""Symbolic tail sums of the cubic B- and E-detour coefficient forms (planning). For a bilinear form
sum_{a small, o} K(a, o) u_a u_{n+o} with disjoint blocks, group by d = a + o (index sum n + d); within a group the
monomial u_a u_{n+d-a} grows with a (LC transfers), so the form is >= 0 by transfers iff every tail sum
T_k(d) = sum_{a >= k} K(a, d - a) is >= 0. Prints, per form, the tail sums that have a negative coefficient after
n = n0 + m (l >= 0, m >= 0). Usage: cubic_tails.py"""
import sys, os
import sympy as sp
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(H, '..', 'cubic'))
from kappa_sym import kap, l, n
sys.argv = sys.argv[:1]
src = open(os.path.join(H, '..', 'cubic', 'edetour_cert.py')).read().split('TG = {')[0]
g = {'__file__': os.path.join(H, '..', 'cubic', 'edetour_cert.py')}; exec(src, g)
assert g['l'] == l or str(g['l']) == 'l'
KE = g['K']; lE, nE = g['l'], g['n']
m = sp.Symbol('m', nonnegative=True)
def tails(F, amax):
    out = {}
    ds = sorted(set(a + o for (a, o) in F))
    for d in ds:
        for k in range(0, amax + 1):
            T = sp.expand(sum(F.get((a, d - a), 0) for a in range(k, amax + 1)))
            if T != 0: out[(d, k)] = T
    return out
def negcoef(T, nv, lv, n0):
    P = sp.Poly(sp.expand(T.subs(nv, n0 + m)), lv, m)
    return [(mo, c) for mo, c in zip(P.monoms(), P.coeffs()) if c < 0]
B = {'rt': ['rt'], 'tt': ['tt'], 'ts': ['ts'], 'taus': ['taus'], 'ss': ['ss'], 'ttau': ['ttau'], 'ttau+74rs': ['ttau', 'rs']}
print('B detour, n >= 6:')
for name, parts in B.items():
    F = {}
    for p in parts:
        w = sp.Rational(7, 4) if p == 'rs' else 1
        for k, v in kap(p).items(): F[k] = sp.expand(F.get(k, 0) + w * v)
    bad = {dk: negcoef(T, n, l, 6) for dk, T in tails(F, 2).items()}
    bad = {dk: v for dk, v in bad.items() if v}
    print(f'  {name:10s}', 'OK' if not bad else bad)
EK = {'rtau': [((0, 2), 1)], 'ttau': [((1, 2), 1)], 'ttau+74rs': [((1, 2), 1), ((0, 3), sp.Rational(7, 4))],
      'ts': [((1, 3), 1)], 'tautau': [((2, 2), 1)], 'taus': [((2, 3), 1)], 'ss': [((3, 3), 1)]}
print('E detour, n >= 7:')
for name, parts in EK.items():
    F = {}
    for key, w in parts:
        for k, v in KE.get(key, {}).items(): F[k] = sp.expand(F.get(k, 0) + w * v)
    bad = {dk: negcoef(T, nE, lE, 7) for dk, T in tails(F, 3).items()}
    bad = {dk: v for dk, v in bad.items() if v}
    print(f'  {name:10s}', 'OK' if not bad else bad)
