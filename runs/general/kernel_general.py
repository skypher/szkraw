"""General-profile kernel equation: L_z = (1 + t z - z^2) sum_k (s_k/k!) z^(k-1) d_z^k + T z.
For monomials S^a Z^r (S = z + w, Z = z w) compute G = (L_z - L_w)(S^a Z^r)/(z - w) in the (S, Z) basis and list the
shifts (r', a') - (r, a) with their coefficients."""
import sympy as sp
z, w, t, T, S, Z = sp.symbols('z w t T S Z')
K = 3
s = sp.symbols(f's1:{K+1}')
def Lop(f, v):
    out = T*v*f
    for k in range(1, K+1):
        out += (1 + t*v - v**2)*s[k-1]/sp.factorial(k)*v**(k-1)*sp.diff(f, v, k)
    return out
def to_SZ(expr):
    # symmetric polynomial in z, w -> polynomial in S, Z
    p = sp.Poly(sp.expand(expr), z, w); res = 0
    while not p.is_zero:
        (i, j), c = max(p.terms(), key=lambda m: (m[0][0], m[0][1]))
        # leading monomial z^i w^j with i >= j: subtract c * S^(i-j) Z^j
        term = c*S**(i - j)*Z**j
        res += term
        p = p - sp.Poly(sp.expand(c*(z + w)**(i - j)*(z*w)**j), z, w)
    return sp.expand(res)
shifts = {}
for a in range(0, 6):
    for r in range(0, 4):
        M = (z + w)**a*(z*w)**r
        G = sp.cancel(sp.expand(Lop(M, z) - Lop(M, w))/(z - w))
        GSZ = to_SZ(G)
        for (da, dr), c in sp.Poly(GSZ, S, Z).terms():
            key = (dr - r, da - a)
            shifts.setdefault(key, []).append(((r, a), sp.factor(c)))
for key in sorted(shifts):
    print('shift (dr, da) =', key, ':', shifts[key][:3])
