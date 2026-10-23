"""Planning test: the cubic B form kappa_ttau + 7/4 kappa_rsigma at n = 2..5 — LP-certifiable by LC transfers,
moves u_j (l u_1 - u_0) and monomials at large l? Usage: cubicB74_large_l.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cubicB_lp_test2 import form, lp
for nv in (2, 3, 4, 5):
    row = []
    for lv in (10, 20, 50, 100, 300, 1000):
        if (lv, nv) == (0, 2): continue
        row.append(f'{lv}:' + ('+' if lp(form('ttau+74rs', lv, nv), lv, nv + 2, True) else '-'))
    print(f'n={nv}', ' '.join(row), flush=True)
