"""Planning test (float LP): cubic E-detour coefficient forms (runs/cubic/edetour_cert.py, MU = 3) as nonnegative
combinations of LC transfers, moves u_j (l u_1 - u_0) and monomials, at numeric (l, n), n >= 3. Usage: cubicE_lp_test.py"""
import sys, os
import numpy as np, sympy as sp
sys.argv = sys.argv[:1]
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic'))
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic', 'edetour_cert.py')).read()
src = src.split('TG = {')[0]
g = {'__file__': os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cubic', 'edetour_cert.py')}; exec(src, g)
K, l, n = g['K'], g['l'], g['n']
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cubicB_lp_test2 import lp
TG = {'rtau': [((0, 2), 1)], 'ttau': [((1, 2), 1)], 'ttau+74rs': [((1, 2), 1), ((0, 3), sp.Rational(7, 4))],
      'ts': [((1, 3), 1)], 'tautau': [((2, 2), 1)], 'taus': [((2, 3), 1)], 'ss': [((3, 3), 1)]}
def form(name, lv, nv):
    F = {}
    for key, w in TG[name]:
        for (a, o), v in K.get(key, {}).items():
            k = tuple(sorted((a, nv + o))); F[k] = F.get(k, 0) + float(w * v.subs({l: lv, n: nv}))
    return F
for use_z in (False, True):
    print('z-moves' if use_z else 'transfers only')
    for name in TG:
        row = []
        for nv in (3, 4, 5, 6, 8):
            s = ''.join('+' if lp(form(name, lv, nv), lv, nv + 3, use_z) else '-' for lv in (0, 1, 2, 3, 5, 10))
            row.append(s)
        print(f'  {name:10s}', ' '.join(row), flush=True)
