"""Cubic ratios: regrouped move families for the resummation (exact, random log-concave profiles, u = r sig/(t tau)).
V^q_n = n (t + tau (l+n-1)) f_{n-1} (the quadratic part of V; its detour is that of Theorem 8.11),
E'_n = w_n + x_n + n sig C(l+n-1, 2) f_{n-1} (W + X + the sigma part of V),
G3_n = sigma part of E' / sigma = n C(l+n-1,2) f_{n-1} + C(n,2)(l+n-2) f_{n-2} + C(n,3) f_{n-3}.
Reports min detour ratios B_0(l,a) Y_{j-1}(l+1,a-2) / (c_{l+1} Y_j(l,a)) (j >= 2), the f-only ratio for G3 with
B_0 replaced by C(a,2) rho(l+1) f_2(l), and the key ratio A0 B0' + B0 A0'' vs c (4 H1 - gV V^q_1 - gE E'_1).
Usage: families.py Ns per u seed"""
import sys, math, random, time
from fractions import Fraction as F
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'varratio'))
from hform import lc_seq
KEYS = {'(2,1)': (F(2), F(1)), '(20/9,4/3)': (F(20, 9), F(4, 3)), '(2,0)': (F(2), F(0)), '(1,1)': (F(1), F(1))}
def check(d, r, t, tau, sig, st):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * math.comb(x, 2) + sig * math.comb(x, 3)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    f = lambda n, l: dif(d, n, l) if n >= 0 else F(0)
    phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rho(l + n)) * f(n, l)
    vq = lambda n, l: n * (t + tau * (l + n - 1)) * f(n - 1, l)
    g3 = lambda n, l: n * math.comb(l + n - 1, 2) * f(n - 1, l) + math.comb(n, 2) * (l + n - 2) * f(n - 2, l) + math.comb(n, 3) * f(n - 3, l)
    wt = lambda n, l: math.comb(n, 2) * tau * f(n - 2, l)
    e2 = lambda n, l: wt(n, l) + sig * g3(n, l)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(max(p, 0), a + 1))
    up = lambda k, v: st.__setitem__(k, min(st.get(k, v), v))
    for l in range(N):
        for a in range(N + 1 - l):
            for n in range(1, a + 1):
                assert dif(b, n, l) == h(n, l) - vq(n, l) - e2(n, l), 'split'
            cc = c[l + 1]; B0 = W(phi, 2, 0, l, a); B0f = math.comb(a, 2) * rho(l + 1) * f(2, l) if a >= 2 else F(0)
            for j in range(2, N + 1):
                if a < 2 * j + 1: break
                for name, s in (('Vq', vq), ('E2', e2), ('G3', g3), ('Wt', wt)):
                    Y = W(s, 2 * j + 1, j, l, a); Yp = W(s, 2 * j - 1, j - 1, l + 1, a - 2)
                    if Y > 0:
                        up('mu_' + name, B0 * Yp / (cc * Y))
                        if name == 'G3': up('muf_G3', B0f * Yp / (cc * Y))
                    elif Y < 0: up('neg_' + name, Y)
            if a >= 3:
                lhs = (b[l + a] - b[l]) * W(phi, 2, 0, l + 1, a - 1) + B0 * (b[l + a - 1] - b[l + 1])
                H1, V1, E1 = (W(s, 3, 1, l, a) for s in (h, vq, e2))
                for kn, (gV, gE) in KEYS.items():
                    rhs = cc * (4 * H1 - gV * V1 - gE * E1)
                    if rhs > 0: up('key' + kn, lhs / rhs)
if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); u = F(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
    st = {}; tot = 0; t0 = time.time()
    for N in Ns:
        for _ in range(per):
            sg = lc_seq(rng, N)
            Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
            d = [z / Dd[N] for z in Dd]
            r = F(rng.choice([1, 10, 50, 90, 99, 999])) / (1000 if rng.random() < .3 else 100); r = min(r, F(999, 1000))
            t1, tau1 = F(rng.choice([1, 1000])), F(rng.choice([1, 1000]))
            mk = lambda lam: (lam * t1, lam * tau1, u * lam * t1 * lam * tau1 / r)
            def okb(lam):
                t, tau, sig = mk(lam); rh = lambda z: r + t * z + tau * math.comb(z, 2) + sig * math.comb(z, 3)
                bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
                return rh(N) <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
            lo, hi = F(0), F(1)
            while okb(hi): hi *= 2
            for _ in range(30):
                mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
            lam = lo * (F(rng.randint(1, 10), 10) if rng.random() < .4 else 1)
            check(d, r, *mk(lam), st); tot += 1
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {tot} arrays, {time.time()-t0:.0f}s", flush=True)
    print(', '.join(f'{k}={float(v):.4g}' for k, v in sorted(st.items())))
