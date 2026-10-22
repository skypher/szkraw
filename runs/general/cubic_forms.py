"""Verify closed forms of the cubic kernel recurrence coefficients against the symbolic operator computation:
 source (r,a) -> equation at (r', a'):
 (0,0): T - D_{r+a};  (0,-1): t (D_{r+a} - D_r);  (0,-2): C(a,2)(s2 + r s3) + C(a,3) s3;
 (1,-2): C(a,2)(s2 + r s3) + 2 C(a,3) s3;  (1,-3): -s3 t C(a,3);  (-1,0): -D_r."""
import sympy as sp
from kernel_general import to_SZ
z, w, t, T, S, Z = sp.symbols('z w t T S Z')
s1, s2, s3 = 1, *sp.symbols('s2 s3')
sig = [s1, s2, s3]
Dn = lambda n: n*s1 + sp.binomial(n, 2)*s2 + sp.binomial(n, 3)*s3
def Lop(f, v):
    out = T*v*f
    for k in range(1, 4): out += (1 + t*v - v**2)*sig[k-1]/sp.factorial(k)*v**(k-1)*sp.diff(f, v, k)
    return out
pred = {(0, 0): lambda r, a: T - Dn(r + a), (0, -1): lambda r, a: t*(Dn(r + a) - Dn(r)),
        (0, -2): lambda r, a: sp.binomial(a, 2)*(s2 + r*s3) + sp.binomial(a, 3)*s3,
        (1, -2): lambda r, a: sp.binomial(a, 2)*(s2 + r*s3) + 2*sp.binomial(a, 3)*s3,
        (1, -3): lambda r, a: -s3*t*sp.binomial(a, 3), (-1, 0): lambda r, a: -Dn(r)}
bad = 0; cnt = 0
for a in range(0, 9):
    for r in range(0, 6):
        M = (z + w)**a*(z*w)**r
        G = sp.cancel(sp.expand(Lop(M, z) - Lop(M, w))/(z - w))
        got = {}
        for (da, dr), c in sp.Poly(to_SZ(G), S, Z).terms(): got[(dr - r, da - a)] = c
        for key in set(got) | set(pred):
            exp = sp.expand(pred[key](r, a)) if key in pred else 0
            if sp.expand(got.get(key, 0) - exp) != 0: bad += 1; print('mismatch', key, r, a, got.get(key), exp)
            cnt += 1
print(f'{cnt} coefficients compared, {bad} mismatches')
