"""Smooth deformations QL(t, kappa) of Krawtchouk (RESEARCH.md); exact symbolic diagnostics. Needs sympy.

QL: d_n = b_n + c_n with increments proportional to 1 + t i/N (t >= 0), ratio rho_n = c_n/d_n = r + kappa n/N,
0 <= kappa <= (1-r)/2, 0 < r < 1; Q is kappa = 0, L is t = 0, K(N,r) is t = kappa = 0. With the slack
s = (1-r)/2 - kappa >= 0, every linearization coefficient is computed as a rational function of (kappa, s, t)
(r = 1 - 2 kappa - 2 s), and numerator and denominator are homogenized in (kappa, s) by r + 2 kappa + 2 s = 1.
If all coefficients of both, as polynomials in (r, kappa, s, t), have one sign, the coefficient is manifestly
nonnegative on the whole parameter region; this proves property (P) for that size.
"""
import argparse
import time
import sympy as sp

r, kap, s, t = sp.symbols('r kappa s t', nonnegative=True)

def table(N, mode):
    kk = 0 if mode == 'Q' else kap
    tt = 0 if mode == 'L' else t
    rr = 1 - 2*kk - 2*s
    d = [sp.Integer(0)]
    for i in range(1, N+1): d.append(d[-1] + 1 + tt*sp.Rational(i, N))
    d = [sp.together(x/d[-1]) for x in d]
    rho = [rr + kk*sp.Rational(n, N) for n in range(N+1)]
    a = [1 - x for x in d]; b = [(1 - p)*x for p, x in zip(rho, d)]; c = [p*x for p, x in zip(rho, d)]
    size = N + 1
    cur = [[sp.Integer(int(i == j)) for j in range(size)] for i in range(size)]
    prev = [[sp.Integer(0)]*size for _ in range(size)]
    res = [cur]
    for m in range(size - 1):
        nxt = [[sp.cancel(((b[i] - b[m])*cur[i][j] - c[m]*prev[i][j] + (c[i]*cur[i-1][j] if i else 0)
                           + (a[i]*cur[i+1][j] if i + 1 < size else 0))/a[m]) for j in range(size)] for i in range(size)]
        res.append(nxt); prev, cur = cur, nxt
    return res

def homog(poly_expr, mode):
    gens = [x for x in (kap, s) if not (mode == 'Q' and x is kap)]
    P = sp.Poly(sp.expand(poly_expr), *gens, t)
    D = max(sum(m[:-1]) for m in P.monoms())
    h = r + 2*kap + 2*s if mode != 'Q' else r + 2*s
    out = sum(cf*sp.Mul(*[g**e for g, e in zip(gens, m[:-1])])*t**m[-1]*h**(D - sum(m[:-1])) for m, cf in zip(P.monoms(), P.coeffs()))
    return sp.Poly(sp.expand(out), r, kap, s, t)

def check(N, mode):
    T = table(N, mode); total = 0; bad = []
    for m in range(N+1):
        for n in range(m, N+1):
            for k in range(N+1):
                g = T[m][n][k]
                if g == 0: continue
                total += 1
                num, den = sp.fraction(sp.factor(g))
                pn, pd = homog(num, mode), homog(den, mode)
                sg = 1 if all(c > 0 for c in pd.coeffs()) else (-1 if all(c < 0 for c in pd.coeffs()) else 0)
                if sg == 0 or not all(c*sg >= 0 for c in pn.coeffs()): bad.append((m, n, k))
    return total, bad

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--modes', default='Q,L,QL'); ap.add_argument('--sizes', default='3,4')
    a = ap.parse_args()
    for mode in a.modes.split(','):
        for N in [int(x) for x in a.sizes.split(',')]:
            t0 = time.time(); total, bad = check(N, mode)
            print(f'{mode} N={N}: {total} nonzero coefficients; not manifestly nonnegative: {len(bad)}'
                  + (f' (first {bad[:3]})' if bad else '') + f' ({time.time()-t0:.0f}s)', flush=True)

if __name__ == '__main__':
    main()
