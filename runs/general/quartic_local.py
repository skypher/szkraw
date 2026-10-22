"""Quartic profiles: local domination inequalities for the kernel-positivity induction.
Moves into node (r+1, a) (source -> weight / D_{r+1}):
  (r, a): T - D_{r+a};  (r, a+1): t A(r, a+1);  (r, a+2): B(r, a+2);  (r-1, a+2): B'(r-1, a+2)
  (r-1, a+3): -t W3(r-1, a+3);  (r-1, a+4): -W4(a+4);  (r-2, a+4): -W4(a+4)
with A, B, B', W3, W4 the symbolic-exponent coefficients (cubic_symbolic.py 4). Hypothesis: D_r c_{r,a} >= kt Vt + kB VB + kP VB'.
Source-wise conditions at node (r+1, a):
 (I3)  (1-kt) A(r,a+1) kB B(r-1,a+3)/D_r + (1-kB) B(r,a+2) kt A(r-1,a+3)/D_r >= W3(r-1,a+3)          [r >= 1]
 (I4a) (1-kB) B(r,a+2) kB B(r-1,a+4)/D_r >= W4(a+4)                                               [r >= 1]
 (I4b) (1-kB) B(r,a+2) kP B'(r-2,a+4)/D_r + (1-kP) B'(r-1,a+2) kB B(r-2,a+4)/D_{r-1} >= W4(a+4)  [r >= 2]
Grid test of min LHS/RHS for LC (x-parametrization) and non-LC sigma; then coefficient test in LC coordinates."""
import sys, itertools, random
import sympy as sp
from cubic_symbolic import G
a_, r_, t_, T_ = sp.symbols('a r t T')
s2, s3, s4 = sp.symbols('s2 s3 s4')
g = G(4, [sp.Integer(1), s2, s3, s4])
Dn = lambda n: n + sp.binomial(n, 2)*s2 + sp.binomial(n, 3)*s3 + sp.binomial(n, 4)*s4
A = lambda r, a: sp.expand(g[(-1, 0)].subs({a_: a, r_: r})/t_)
B = lambda r, a: sp.expand(g[(-2, 0)].subs({a_: a, r_: r}))
Bp = lambda r, a: sp.expand(g[(-2, 1)].subs({a_: a, r_: r}))
W3 = lambda r, a: sp.expand(-g[(-3, 1)].subs({a_: a, r_: r})/t_)
W4 = lambda a: sp.expand(-g[(-4, 1)].subs({a_: a}))
assert sp.expand(g[(-4, 2)] - g[(-4, 1)]) == 0
# sanity: A(r,a) = D_{r+a} - D_r
assert sp.simplify(sp.expand_func(A(r_, a_) - (Dn(r_ + a_) - Dn(r_)))) == 0, 'A form'
def ratios(kt, kB, kP, r, a, sv):
    sub = dict(zip((s2, s3, s4), sv)); f = lambda e: float(e.subs(sub))
    Dr = f(Dn(r)); out = {}
    out['I3'] = (f((1-kt)*A(r, a+1)*kB*B(r-1, a+3) + (1-kB)*B(r, a+2)*kt*A(r-1, a+3))/Dr) / max(f(W3(r-1, a+3)), 1e-300)
    out['I4a'] = (f((1-kB)*B(r, a+2)*kB*B(r-1, a+4))/Dr) / max(f(W4(a+4)), 1e-300)
    if r >= 2:
        out['I4b'] = (f((1-kB)*B(r, a+2)*kP*Bp(r-2, a+4))/Dr + f((1-kP)*Bp(r-1, a+2)*kB*B(r-2, a+4))/f(Dn(r-1))) / max(f(W4(a+4)), 1e-300)
    return out
if __name__ == '__main__':
    rng = random.Random(1)
    def lc_sample():
        x = [rng.choice([0, 0.001, 0.1, 1, 10]) for _ in range(3)]
        rho1, rho2, rho3 = x[0] + x[1] + x[2], x[1] + x[2], x[2]
        return (rho1, rho1*rho2, rho1*rho2*rho3)
    def nonlc_sample():
        return tuple(rng.choice([0, 0.001, 0.1, 1, 10]) for _ in range(3))
    for kt, kB, kP in ((0.5, 0.5, 0.5), (0.5, 0.4, 0.5), (0.4, 0.5, 0.5), (0.5, 0.5, 0.3)):
        for name, samp in (('LC', lc_sample), ('nonLC', nonlc_sample)):
            worst = {}
            for _ in range(300):
                sv = samp()
                if sv[2] == 0: continue
                for r in (1, 2, 3, 5, 10, 30):
                    for a in (0, 1, 2, 4, 8, 20):
                        for key, v in ratios(kt, kB, kP, r, a, sv).items():
                            if key not in worst or v < worst[key][0]: worst[key] = (v, r, a, sv)
            print(f'k=({kt},{kB},{kP}) {name:5s}: ' + '; '.join(f'{k} min {v[0]:.3f} at r={v[1]} a={v[2]} s={tuple(round(x, 4) for x in v[3])}' for k, v in sorted(worst.items())), flush=True)
