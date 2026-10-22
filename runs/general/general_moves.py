import sys, sympy as sp
from cubic_symbolic import G
from quartic_binom import binom_basis
a_, r_, t_ = sp.symbols('a r t')
K = int(sys.argv[1])
sig = [sp.Integer(1)] + list(sp.symbols(f's2:{K+1}'))
g = G(K, sig)
for (da, dr), v in sorted(g.items()):
    if (da, dr) in ((0, 0), (0, -1)): continue
    node = (dr + 1, da)
    v0 = sp.expand(v.subs(t_, 0)); v1 = sp.expand(sp.diff(v, t_))
    parts = []
    if v0 != 0: parts.append(('const', binom_basis(v0, K, K)))
    if v1 != 0: parts.append(('t', binom_basis(v1, K, K)))
    print(f'node move (dr, da) = {node}:', parts)
