"""Structure of exact key certificates: nonzero multipliers grouped by generator type (same order as key_cert_exact.build).
Usage: key_cert_inspect.py a (rand seed | geo w)"""
import sys, random
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_cert_lp import lc_u
from key_cert_exact import build, certify
a = int(sys.argv[1])
if sys.argv[2] == 'rand': u = lc_u(random.Random(int(sys.argv[3])), a + 3); kind = 'rand'
else:
    w = sp.Rational(sys.argv[3]); u = [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]; kind = f'geo w={w}'
names = [('g*P', m, k) for m in range(a) for k in range(a + 1)] + [('b*P', m, k) for m in range(a + 1) for k in range(a + 1)] + \
        [('P', k) for k in range(a + 1)] + [('PP', i, j) for i in range(a + 1) for j in range(i, a + 1)] + \
        [('LC', i, j) for i in range(1, a + 1) for j in range(i, a)]
A, bv = build(u, a, True)
verdict, x = certify(A, bv)
print(kind, 'a =', a, verdict)
if x:
    for typ in ['g*P', 'b*P', 'P', 'PP', 'LC']:
        items = [(names[i][1:], x[i]) for i in range(len(x)) if x[i] != 0 and names[i][0] == typ]
        print(f'  {typ}: {len(items)}:', ' '.join(f'{n}' for n, v in items[:40]))
