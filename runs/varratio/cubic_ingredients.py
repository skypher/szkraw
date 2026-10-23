"""Exact check of the Theorem 8.11 proof ingredients for cubic ratios rho(x) = r + t x + tau C(x,2) + sig C(x,3),
t, tau >= 0, r sig = u t tau, b nondecreasing, on random log-concave Newton profiles.
psi_n = h_n - v_n - w_n - x_n: h = (1-rho(l+n)) f_n, v = n Drho(l+n-1) f_{n-1}, w = C(n,2) D2rho(l+n-2) f_{n-2},
x = C(n,3) sig f_{n-3}. Reports, over all sources (l,a) in Omega, the minimum detour ratios
mu_Y = B_0(l,a) Y_{j-1}(l+1,a-2) / (c_{l+1} Y_j(l,a)) for Y in B (j>=1), H, V, W, X (j>=2), C' (j>=1),
the minimum of the pointwise quad-B ratio (n+1)(n+2) phi_2(l) phi_n(l+1) / (8(n-1) c_{l+1} phi_{n+2}(l)),
and the key inequality A0 B0' + B0 A0'' >= c (4 H1 - gV V1 - gW W1 - gX X1) for two constant sets.
Usage: cubic_ingredients.py Ns per us seed [adv]"""
import sys, math, random, time
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from hform import lc_seq

GAMMAS = {'(4/3,0,0)': (F(4, 3), F(0), F(0)), '(0,0,0)': (F(0), F(0), F(0)), '(2,0,0)': (F(2), F(0), F(0)), '(20/9,4/3,4/3)': (F(20, 9), F(4, 3), F(4, 3))}

def check(d, r, t, tau, sig, stats):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    D1 = lambda x: t + tau * x + sig * math.comb(x, 2); D2 = lambda x: tau + sig * x
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    f = lambda n, l: dif(d, n, l)
    phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rho(l + n)) * f(n, l)
    v = lambda n, l: n * D1(l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
    w = lambda n, l: math.comb(n, 2) * D2(l + n - 2) * f(n - 2, l) if n >= 2 else F(0)
    x = lambda n, l: math.comb(n, 3) * sig * f(n - 3, l) if n >= 3 else F(0)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    upd = lambda k, val: stats.__setitem__(k, min(stats.get(k, val), val))
    for l in range(N):
        for a in range(N + 1 - l):
            for n in range(1, a + 1):
                assert dif(b, n, l) == h(n, l) - v(n, l) - w(n, l) - x(n, l), ('split', l, n)
            cc = c[l + 1]; B0 = W(phi, 2, 0, l, a)
            for n in range(2, a - 1):
                rhs = 8 * (n - 1) * cc * phi(n + 2, l)
                if rhs > 0: upd('quadB', (n + 1) * (n + 2) * phi(2, l) * phi(n, l + 1) / rhs)
            for j in range(1, N + 1):
                if a < 2 * j + 1: break
                fams = [('B', 1, lambda L, A, J: W(phi, 2 * J + 2, J, L, A)), ('H', 2, lambda L, A, J: W(h, 2 * J + 1, J, L, A)),
                        ('V', 2, lambda L, A, J: W(v, 2 * J + 1, J, L, A)), ('W', 2, lambda L, A, J: W(w, 2 * J + 1, J, L, A)),
                        ('X', 2, lambda L, A, J: W(x, 2 * J + 1, J, L, A)),
                        ('WX', 2, lambda L, A, J: W(lambda n, ll: w(n, ll) + x(n, ll), 2 * J + 1, J, L, A)), ('C', 1, lambda L, A, J: W(f, 2 * J + 2, J + 1, L, A))]
                for name, jmin, Wf in fams:
                    if j < jmin: continue
                    Y = Wf(l, a, j)
                    if Y > 0: upd('mu_' + name, B0 * (Wf(l + 1, a - 2, j - 1) if a >= 2 else 0) / (cc * Y))
                    elif Y < 0: upd('neg_' + name, Y)
            if a >= 3:
                A0 = b[l + a] - b[l]; A0b = b[l + a - 1] - b[l + 1]
                lhs = A0 * W(phi, 2, 0, l + 1, a - 1) + B0 * A0b
                H1, V1, W1, X1 = (W(s, 3, 1, l, a) for s in (h, v, w, x))
                for gname, (gV, gW, gX) in GAMMAS.items():
                    rhs = cc * (4 * H1 - gV * V1 - gW * W1 - gX * X1)
                    if rhs > 0: upd('key' + gname, lhs / rhs)

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); us = [F(z) for z in sys.argv[3].split(',')]
    rng = random.Random(int(sys.argv[4])); t0 = time.time()
    ADV = len(sys.argv) > 5 and sys.argv[5] == 'adv'
    for u in us:
        stats = {}; tot = 0
        for N in Ns:
            for _ in range(per):
                sg = lc_seq(rng, N)
                Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
                d = [z / Dd[N] for z in Dd]
                if ADV:
                    r = F(rng.choice([1, 10, 50, 90, 99, 999])) / (1000 if rng.random() < .3 else 100); r = min(r, F(999, 1000))
                    t1, tau1 = F(rng.choice([1, 1000])), F(rng.choice([1, 1000]))
                else:
                    r = F(rng.choice([1, 2, 5, 10, 16, 19, 99])) / (100 if rng.random() < .2 else 20)
                    r = min(r, F(99, 100))
                    t1, tau1 = F(rng.choice([1, 1, 2, 5])), F(rng.choice([1, 1, 3, 10]))
                def mk(lam): return lam * t1, lam * tau1, u * lam * t1 * lam * tau1 / r
                def okb(lam):
                    t, tau, sig = mk(lam); rh = lambda z: r + t * z + tau * math.comb(z, 2) + sig * math.comb(z, 3)
                    bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
                    return rh(N) <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
                lo, hi = F(0), F(1)
                while okb(hi): hi *= 2
                for _ in range(30):
                    mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
                lam = lo * (F(rng.randint(1, 10), 10) if rng.random() < .4 else 1)
                check(d, r, *mk(lam), stats); tot += 1
            print(f"[{time.strftime('%H:%M:%S')}] u={u} N={N} done, {tot} arrays, {time.time()-t0:.0f}s", flush=True)
        print(f"u={u}: " + ', '.join(f"{k}={float(v):.4g}" for k, v in sorted(stats.items())), flush=True)
