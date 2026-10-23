"""Inspect sparse degree-2 certificates for the key (minimize total multiplier weight); group used generators by type.
Usage: key_cert_inspect.py a w (geometric far-field u) | a rand seed"""
import sys, random, math
import sympy as sp
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_cert_lp import key_poly, lc_u
a = int(sys.argv[1])
if sys.argv[2] == 'rand': u = lc_u(random.Random(int(sys.argv[3])), a + 3); kind = 'rand'
else:
    w = sp.Rational(sys.argv[2]); u = [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]; kind = f'geo w={w}'
key, P, b = key_poly(u, a); Pv = P[:a + 1]
gens, names = [], []
for m in range(a):
    g = sp.expand(b(m + 1) - b(m))
    for k in range(a + 1): gens.append(sp.expand(g * Pv[k])); names.append(('g*P', m, k))
for m in range(a + 1):
    for k in range(a + 1): gens.append(sp.expand(b(m) * Pv[k])); names.append(('b*P', m, k))
for k in range(a + 1): gens.append(Pv[k]); names.append(('P', k))
for i in range(a + 1):
    for j in range(i, a + 1): gens.append(Pv[i] * Pv[j]); names.append(('PP', i, j))
for i in range(1, a + 1):
    for j in range(i, a):
        gens.append(sp.expand(Pv[i] * Pv[j] - Pv[i - 1] * Pv[j + 1])); names.append(('LC', i, j))
polys = [sp.Poly(g, *Pv) for g in gens]; Pk = sp.Poly(key, *Pv)
monos = sorted(set(m for p in polys + [Pk] for m in p.monoms())); idx = {m: t for t, m in enumerate(monos)}
A = np.zeros((len(monos), len(polys)))
for col, p in enumerate(polys):
    for m, v in zip(p.monoms(), p.coeffs()): A[idx[m], col] = float(v)
bvec = np.zeros(len(monos))
for m, v in zip(Pk.monoms(), Pk.coeffs()): bvec[idx[m]] = float(v)
res = linprog(np.ones(len(polys)), A_eq=A, b_eq=bvec, bounds=[(0, None)] * len(polys), method='highs')
print(kind, 'a =', a, 'status', res.status)
if res.status == 0:
    used = [(names[i], res.x[i]) for i in range(len(polys)) if res.x[i] > 1e-9 * max(1, abs(bvec).max())]
    for typ in ['g*P', 'b*P', 'P', 'PP', 'LC']:
        items = [(n, v) for n, v in used if n[0] == typ]
        print(f'  {typ}: {len(items)} used:', ', '.join(f'{n[1:]}={v:.3g}' for n, v in sorted(items, key=lambda z: -z[1])[:10]))
