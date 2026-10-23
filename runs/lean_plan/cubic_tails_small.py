"""Small-n tail sums of the cubic B forms (n = 2..5) and E forms (n = 3..6), as polynomials in l (planning).
The bilinear form sum K(a,o) u_a u_{n+o} is regrouped into monomials u_i u_j (i <= j); per index sum s the chain
u_0 u_s <= u_1 u_{s-1} <= ... is increasing (LC), so transfers certify the form iff every tail sum (from the most
balanced pair down) is >= 0. Prints the tails that are negative somewhere on l >= 0 (checked at l = 0..40 and by
coefficient signs after l -> l + 1). Also checks kap() against small_n_forms.forms() for n = 2, 3. Usage: cubic_tails_small.py"""
import sys, os
import sympy as sp
H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(H, '..', 'cubic'))
from kappa_sym import kap, l, n
from small_n_forms import forms, u as U, l as Ls
sys.argv = sys.argv[:1]
src = open(os.path.join(H, '..', 'cubic', 'edetour_cert.py')).read().split('TG = {')[0]
g = {'__file__': os.path.join(H, '..', 'cubic', 'edetour_cert.py')}; exec(src, g)
KE, lE, nE = g['K'], g['l'], g['n']
def mono(F, nv, lv_sym, lsub):
    M = {}
    for (a, o), v in F.items():
        b = nv + o
        if b < 0: continue
        k = tuple(sorted((a, b))); M[k] = sp.expand(M.get(k, 0) + v.subs({lv_sym: lsub}))
    return {k: v for k, v in M.items() if v != 0}
# cross-check kap vs forms at n = 2, 3
for nv in (2, 3):
    for name in ('ts', 'ttau', 'rs', 'tt', 'rt', 'taus', 'ss'):
        M = mono({k: v.subs(n, nv) for k, v in kap(name).items()}, nv, l, Ls)
        P = sp.expand(sum(c * U[i] * U[j] for (i, j), c in M.items()))
        assert sp.expand(P - forms(nv)[name]) == 0, (nv, name)
print('kap = small_n_forms at n = 2, 3')
def tails(M):
    out = {}
    for s in sorted(set(i + j for i, j in M)):
        pairs = sorted([(i, j) for (i, j) in M if i + j == s], reverse=True)  # most balanced first
        top = s // 2
        acc = 0
        for i in range(top, -1, -1):
            acc = sp.expand(acc + M.get((i, s - i), 0))
            if acc != 0: out[(s, i)] = acc
    return out
def neg_somewhere(T, lv):
    if any(T.subs(lv, k) < 0 for k in range(0, 41)): return 'NEG'
    P = sp.Poly(sp.expand(T.subs(lv, lv + 1)), lv)
    return 'mixed' if any(c < 0 for c in P.coeffs()) else None
B = {'rt': ['rt'], 'tt': ['tt'], 'ts': ['ts'], 'taus': ['taus'], 'ss': ['ss'], 'ttau': ['ttau'], 'ttau+74rs': ['ttau', 'rs']}
print('B small n (tails negative somewhere / with mixed signs):')
for name, parts in B.items():
    for nv in (2, 3, 4, 5):
        F = {}
        for p in parts:
            w = sp.Rational(7, 4) if p == 'rs' else 1
            for k, v in kap(p).items(): F[k] = sp.expand(F.get(k, 0) + w * v.subs(n, nv))
        M = mono(F, nv, l, l)
        bad = {k: (neg_somewhere(T, l), sp.factor(T)) for k, T in tails(M).items() if neg_somewhere(T, l)}
        if bad: print(f'  {name} n={nv}:', bad)
EK = {'rtau': [((0, 2), 1)], 'ttau': [((1, 2), 1)], 'ttau+74rs': [((1, 2), 1), ((0, 3), sp.Rational(7, 4))],
      'ts': [((1, 3), 1)], 'tautau': [((2, 2), 1)], 'taus': [((2, 3), 1)], 'ss': [((3, 3), 1)]}
print('E small n:')
for name, parts in EK.items():
    for nv in (3, 4, 5, 6):
        F = {}
        for key, w in parts:
            for k, v in KE.get(key, {}).items(): F[k] = sp.expand(F.get(k, 0) + w * v.subs(nE, nv))
        M = mono(F, nv, lE, lE)
        bad = {k: (neg_somewhere(T, lE), sp.factor(T)) for k, T in tails(M).items() if neg_somewhere(T, lE)}
        if bad: print(f'  {name} n={nv}:', bad)
print('done')
print('B ttau+74rs with z-moves (move each negative u_0 u_s coefficient to l * u_1 u_s):')
for nv in (2, 3, 4, 5):
    F = {}
    for p in ('ttau', 'rs'):
        w = sp.Rational(7, 4) if p == 'rs' else 1
        for k, v in kap(p).items(): F[k] = sp.expand(F.get(k, 0) + w * v.subs(n, nv))
    M = mono(F, nv, l, l)
    moved = []
    for (i, j), c in sorted(M.items()):
        if i == 0 and j >= 1 and neg_somewhere(c, l):
            sgn = 'nonpos' if all(c.subs(l, k) <= 0 for k in range(0, 41)) else 'MIXED'
            moved.append(((0, j), sp.factor(c), sgn))
    M2 = dict(M)
    for (i, j), c, sgn in moved:
        M2[(0, j)] = 0
        k = tuple(sorted((1, j))); M2[k] = sp.expand(M2.get(k, 0) + l * c)
    M2 = {k: v for k, v in M2.items() if v != 0}
    bad = {k: (neg_somewhere(T, l), sp.factor(T)) for k, T in tails(M2).items() if neg_somewhere(T, l)}
    print(f'  n={nv}: moved {moved}')
    print(f'        remaining bad tails: {bad}')
print('B ttau+rs (u = 1, the theorem as stated), transfers only:')
for nv in (2, 3, 4, 5):
    F = {}
    for p in ('ttau', 'rs'):
        for k, v in kap(p).items(): F[k] = sp.expand(F.get(k, 0) + v.subs(n, nv))
    M = mono(F, nv, l, l)
    bad = {k: (neg_somewhere(T, l), sp.factor(T)) for k, T in tails(M).items() if neg_somewhere(T, l)}
    print(f'  n={nv}:', bad if bad else 'OK')
