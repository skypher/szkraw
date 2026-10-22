import sympy as sp, sys
from kernel_general import to_SZ
z, w, t, T, S, Z = sp.symbols('z w t T S Z')
K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
s = sp.symbols(f's1:{K+1}')
def Lop(f, v):
    out = T*v*f
    for k in range(1, K+1):
        out += (1 + t*v - v**2)*s[k-1]/sp.factorial(k)*v**(k-1)*sp.diff(f, v, k)
    return out
tab = {}
for a in range(0, 7):
    for r in range(0, 4):
        M = (z + w)**a*(z*w)**r
        G = sp.cancel(sp.expand(Lop(M, z) - Lop(M, w))/(z - w))
        for (da, dr), c in sp.Poly(to_SZ(G), S, Z).terms():
            tab.setdefault((dr - r, da - a), {})[(r, a)] = sp.factor(c)
for key in sorted(tab):
    print('shift', key)
    for (r, a), c in sorted(tab[key].items()):
        if a <= 5 and r <= 2: print(f'   (r={r}, a={a}): {c}')
