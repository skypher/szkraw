"""Full key (gamma_V = 2, gamma_W = 0) on geometric profiles d_i = ((1+w)^i - 1)/((1+w)^N - 1) with small w, for
(1) pure quadratic ratios rho = r + tau C(x,2) (Newton (r,0,tau): not LC), and (2) LC ratios rho = r + t x + tau C(x,2)
with t^2 = r tau (boundary of LC). tau = lam * max with b nondecreasing. Reports min key ratio over sources with a >= 3,
and the weakened-key ratio (K') at the same source. Usage: key_full_regime.py Ns ws rs"""
import sys, math
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')

def arrays(N, w, r, mode):
    d = [((1 + w) ** i - 1) / ((1 + w) ** N - 1) for i in range(N + 1)]
    def rho_of(p):  # pure: tau = p, t = 0;  lc: t = p, tau = t^2/r (boundary of LC)
        t, tau = (p, p * p / r) if mode == 'lc' else (F(0), p)
        return lambda x: r + t * x + tau * F(x * (x - 1), 2)
    def ok(tau):
        rh = rho_of(tau); b = [(1 - rh(i)) * d[i] for i in range(N + 1)]
        return rh(N) <= 1 and all(b[i + 1] >= b[i] for i in range(N))
    lo, hi = F(0), F(1)
    for _ in range(40):
        mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return d, rho_of(lo)

def keymin(d, rh):
    N = len(d) - 1
    rv = [rh(i) for i in range(2 * N + 3)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    c = [rv[i] * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    f = lambda n, l: dif(d, n, l); phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rv[l + n]) * f(n, l)
    v = lambda n, l: n * dif(rv, 1, l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    best = None
    for l in range(N):
        for a in range(3, N + 1 - l):
            lhs = (b[l + a] - b[l]) * W(phi, 2, 0, l + 1, a - 1) + W(phi, 2, 0, l, a) * (b[l + a - 1] - b[l + 1])
            rhs = c[l + 1] * (4 * W(h, 3, 1, l, a) - 2 * W(v, 3, 1, l, a))
            Y = sum(math.comb(a, n) * f(n, l) for n in range(2, a + 1)); Yp = sum(math.comb(a - 1, n) * f(n, l + 1) for n in range(2, a))
            lhsw = c[l + 1] / d[l + 1] * ((b[l + a] - b[l]) * Yp + Y * (b[l + a - 1] - b[l + 1]))
            if rhs > 0:
                q = (float(lhs / rhs), float(lhsw / rhs), l, a)
                if best is None or q[0] < best[0]: best = q
    return best

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; ws = [F(z) for z in sys.argv[2].split(',')]; rs = [F(z) for z in sys.argv[3].split(',')]
    for N in Ns:
        for w in ws:
            for r in rs:
                for mode in ['pure', 'lc']:
                    d, rh = arrays(N, w, r, mode)
                    km = keymin(d, rh)
                    if km is None:
                        print(f'N={N} w={w} r={r} {mode}: RHS <= 0 at every source (key trivial)', flush=True); continue
                    print(f'N={N} w={w} r={r} {mode}: min full key ratio {km[0]:.4g} (weakened at same source {km[1]:.4g}) at (l,a)={km[2:]}', flush=True)
