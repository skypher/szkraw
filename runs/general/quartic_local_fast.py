import random
import sympy as sp
from cubic_symbolic import G
a_, r_, t_ = sp.symbols('a r t')
s2, s3, s4 = sp.symbols('s2 s3 s4')
g = G(4, [sp.Integer(1), s2, s3, s4])
args = (r_, a_, s2, s3, s4)
Af = sp.lambdify(args, sp.expand(g[(-1, 0)]/t_)); Bf = sp.lambdify(args, g[(-2, 0)]); Bpf = sp.lambdify(args, g[(-2, 1)])
W3f = sp.lambdify(args, sp.expand(-g[(-3, 1)]/t_)); W4f = sp.lambdify(args, -g[(-4, 1)])
Dn = lambda n, s: n + n*(n-1)/2*s[0] + n*(n-1)*(n-2)/6*s[1] + n*(n-1)*(n-2)*(n-3)/24*s[2]
def q(x, y): return x/y if y > 0 else (float('inf') if x >= 0 else float('-inf'))
def ratios(k, r, a, s):
    kt, kB, kP = k; Dr = Dn(r, s); out = {}
    out['I3'] = q(((1-kt)*Af(r, a+1, *s)*kB*Bf(r-1, a+3, *s) + (1-kB)*Bf(r, a+2, *s)*kt*Af(r-1, a+3, *s))/Dr, W3f(r-1, a+3, *s))
    out['I4a'] = q(((1-kB)*Bf(r, a+2, *s)*kB*Bf(r-1, a+4, *s))/Dr, W4f(r-1, a+4, *s))
    if r >= 2:
        out['I4b'] = q((1-kB)*Bf(r, a+2, *s)*kP*Bpf(r-2, a+4, *s)/Dr + (1-kP)*Bpf(r-1, a+2, *s)*kB*Bf(r-2, a+4, *s)/Dn(r-1, s), W4f(r-2, a+4, *s))
    return out
rng = random.Random(1)
vals = [0, 0.001, 0.01, 0.1, 1, 10, 100]
def lc_sample():
    x = [rng.choice(vals) for _ in range(3)]
    r1, r2, r3 = x[0] + x[1] + x[2], x[1] + x[2], x[2]
    return (r1, r1*r2, r1*r2*r3)
def nonlc_sample(): return tuple(rng.choice(vals) for _ in range(3))
for k in ((0.5, 0.5, 0.5), (0.5, 0.4, 0.5), (0.4, 0.5, 0.5), (0.5, 0.5, 0.3), (0.6, 0.5, 0.5)):
    for name, samp in (('LC', lc_sample), ('nonLC', nonlc_sample)):
        worst = {}
        for _ in range(3000):
            s = samp()
            if s[2] == 0: continue
            for r in (1, 2, 3, 4, 6, 10, 30, 100):
                for a in (0, 1, 2, 3, 5, 8, 20, 60):
                    for key, v in ratios(k, r, a, s).items():
                        if key not in worst or v < worst[key][0]: worst[key] = (v, r, a, s)
        print(f'k={k} {name:5s}: ' + '; '.join(f'{kk} min {v[0]:.3f} (r={v[1]},a={v[2]},s={tuple(round(x, 4) for x in v[3])})' for kk, v in sorted(worst.items())), flush=True)
