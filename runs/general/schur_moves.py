"""Kernel recurrence in the two-variable Schur basis s_{r,a} = Z^r h_a(z,w) (h_a = (z^{a+1} - w^{a+1})/(z - w)).
Compute (L_z - L_w)(Z^r h_a)/(z - w) for symbolic profile of degree K at numeric (r, a), expand in the Schur basis,
and tabulate move signs (target - source)."""
import sys
import sympy as sp
z, w, t, T = sp.symbols('z w t T')
K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
sig = [sp.Integer(1)] + list(sp.symbols(f's2:{K+1}'))
def Lop(f, v):
    out = T*v*f
    for k in range(1, K+1): out += (1 + t*v - v**2)*sig[k-1]/sp.factorial(k)*v**(k-1)*sp.diff(f, v, k)
    return out
def schur(r, a): return sp.expand((z*w)**r*sum(z**i*w**(a - i) for i in range(a + 1)))
def to_schur(expr):
    p = sp.Poly(sp.expand(expr), z, w); res = {}
    while not p.is_zero:
        (i, j), c = max(p.terms(), key=lambda m: (m[0][0] - m[0][1], m[0][0]))
        # leading in z-degree minus w-degree: monomial z^i w^j with i >= j -> Schur (r = j, a = i - j)
        r_, a_ = j, i - j
        res[(r_, a_)] = sp.expand(res.get((r_, a_), 0) + c)
        p = p - sp.Poly(c*schur(r_, a_), z, w)
    return res
moves = {}
for a in range(0, 7):
    for r in range(0, 4):
        G = sp.cancel(sp.expand(Lop(schur(r, a), z) - Lop(schur(r, a), w))/(z - w))
        for (r2, a2), c in to_schur(G).items():
            moves.setdefault((r2 - r, a2 - a), []).append(((r, a), sp.factor(c)))
for key in sorted(moves):
    vals = moves[key]
    signs = set()
    for _, c in vals:
        P = sp.Poly(sp.expand(c), t, T, *sig[1:])
        signs |= {('+' if co > 0 else '-') for co in P.coeffs()}
    print(f'shift (dr, da) = {key}: signs {sorted(signs)}; e.g. {vals[:3]}')
