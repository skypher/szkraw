"""Symbolic-exponent derivation of the kernel recurrence coefficients for a general profile of degree K:
G = (L_z - L_w)(S^a Z^r)/(z - w) with a, r symbols. Terms are kept as {(alpha, beta, p, q): coeff} meaning
coeff * S^(a+alpha) Z^(r+beta) z^p w^q. d/dz: S' = 1, Z' = w. Antisymmetrize, divide by (z - w) using
(z^d - w^d)/(z - w) = h_{d-1}(S, Z), h_n = S h_{n-1} - Z h_{n-2}; collect coefficients of S^(a+alpha) Z^(r+beta).
Compares with the closed forms of cubic_forms.py (K = 3) and prints the K = 4 table."""
import sys
import sympy as sp
a, r, t, T = sp.symbols('a r t T')
def dz(terms):
    out = {}
    def add(k, c):
        out[k] = sp.expand(out.get(k, 0) + c)
    for (al, be, p, q), c in terms.items():
        add((al - 1, be, p, q), c*(a + al))          # d/dS
        add((al, be - 1, p, q + 1), c*(r + be))      # d/dZ * w
        if p: add((al, be, p - 1, q), c*p)           # explicit z
    return {k: v for k, v in out.items() if v != 0}
def Lz(K, sig):
    f = {(0, 0, 0, 0): sp.Integer(1)}
    res = {}
    def add(k, c): res[k] = sp.expand(res.get(k, 0) + c)
    add((0, 0, 1, 0), T)                              # T z f
    der = f
    for k in range(1, K+1):
        der = dz(der)
        for (al, be, p, q), c in der.items():
            base = c*sig[k-1]/sp.factorial(k)
            # (1 + t z - z^2) z^(k-1)
            add((al, be, p + k - 1, q), base)
            add((al, be, p + k, q), base*t)
            add((al, be, p + k + 1, q), -base)
    return {k: v for k, v in res.items() if v != 0}
def hpoly(n):
    S, Z = sp.symbols('S Z'); h = [sp.Integer(1), S]
    while len(h) <= n: h.append(sp.expand(S*h[-1] - Z*h[-2]))
    return sp.Poly(h[n], S, Z)
def G(K, sig):
    L = Lz(K, sig)
    out = {}
    def add(k, c): out[k] = sp.expand(out.get(k, 0) + c)
    # L_z f - L_w f: term c * S^.. Z^.. z^p w^q minus its mirror c * z^q w^p; (z^p w^q - z^q w^p)/(z - w)
    for (al, be, p, q), c in L.items():
        m = min(p, q); dd = abs(p - q)
        if dd == 0: continue
        sign = 1 if p > q else -1
        for (i, j), hc in hpoly(dd - 1).terms():   # S^i Z^j
            add((al + i, be + j + m), sign*c*hc)
    return {k: sp.factor(v) for k, v in out.items() if v != 0}
if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    sig = [sp.Integer(1)] + list(sp.symbols(f's2:{K+1}'))
    g = G(K, sig)
    Dn = lambda n: sum(sp.binomial(n, k)*sig[k-1] for k in range(1, K+1))
    for key in sorted(g): print('shift (da, dr) =', key, ':', g[key])
    if K == 3:
        s2, s3 = sig[1], sig[2]
        C = lambda n, k: sp.expand_func(sp.binomial(n, k))
        Dp = lambda n: n + C(n, 2)*s2 + C(n, 3)*s3
        pred = {(0, 0): T - Dp(r + a), (-1, 0): t*(Dp(r + a) - Dp(r)), (-2, 0): C(a, 2)*(s2 + r*s3) + C(a, 3)*s3,
                (-2, 1): C(a, 2)*(s2 + r*s3) + 2*C(a, 3)*s3, (-3, 1): -s3*t*C(a, 3), (0, -1): -Dp(r)}
        ok = all(sp.simplify(sp.expand(g.get(k, 0) - pred.get(k, 0))) == 0 for k in set(g) | set(pred))
        print('cubic closed forms match the symbolic-exponent derivation:', ok)
