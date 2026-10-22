"""Kernel recurrence in the shifted basis S' = S + t Z (Krawtchouk kernel is (1+Z)^(N-k) S'^k). Compute
(L_z - L_w)(S'^a Z^r)/(z - w) expanded in S'^a' Z^r' for numeric (r, a) and report the sign pattern per shift."""
import sys
import sympy as sp
from kernel_general import to_SZ
z, w, t, T, S, Z, Sp = sp.symbols("z w t T S Z Sp")
K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
sig = [sp.Integer(1)] + list(sp.symbols(f's2:{K+1}'))
def Lop(f, v):
    out = T*v*f
    for k in range(1, K+1): out += (1 + t*v - v**2)*sig[k-1]/sp.factorial(k)*v**(k-1)*sp.diff(f, v, k)
    return out
moves = {}
for a in range(0, 7):
    for r in range(0, 4):
        M = sp.expand((z + w + t*z*w)**a*(z*w)**r)
        G = sp.cancel(sp.expand(Lop(M, z) - Lop(M, w))/(z - w))
        GSZ = to_SZ(G)                                  # in S, Z
        GSp = sp.expand(GSZ.subs(S, Sp - t*Z))          # in S', Z
        for (da, dr), c in sp.Poly(GSp, Sp, Z).terms():
            moves.setdefault((dr - r, da - a), []).append(((r, a), sp.factor(c)))
for key in sorted(moves):
    signs = set()
    for _, c in moves[key]:
        P = sp.Poly(sp.expand(c), t, T, *sig[1:])
        signs |= {('+' if co > 0 else '-') for co in P.coeffs()}
    print(f'shift (dr, da) = {key}: signs {sorted(signs)}; e.g. {moves[key][:2]}')
