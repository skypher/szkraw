"""Exact check of the final (C3) ingredients on random arrays (u = r sig/(t tau), b nondecreasing, LC Newton profile):
split psi_n = h_n - v_n - e_n with v_n = n(t + tau(l+n-1) + sig(C(l,2) + l(n-1))) f_{n-1},
e_n = C(n,2)(tau + sig l) f_{n-2} + sig C(n,3)(3 f_{n-1} + 3 f_{n-2} + f_{n-3}); minimum summed detour ratios
B_0(l,a) Y_{j-1}(l+1,a-2) / (c_{l+1} Y_j(l,a)) for Y = B (j >= 1, needs 4), H (10), V (9/2), E (3), C' (6) (j >= 2 for H,V,E);
key ratio (A0 B0' + B0 A0'') / (c (4 H1 - 2 V1 - E1)) (needs >= 1). Heartbeat per N. Usage: final_ingredients.py Ns per u seed"""
import sys, os, math, random, time
from fractions import Fraction as F
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'varratio'))
from hform import lc_seq
C = math.comb
def check(d, r, t, tau, sig, st):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * C(x, 2) + sig * C(x, 3)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * C(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    f = lambda n, l: dif(d, n, l) if n >= 0 else F(0)
    phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rho(l + n)) * f(n, l)
    v = lambda n, l: n * (t + tau * (l + n - 1) + sig * (C(l, 2) + l * (n - 1))) * f(n - 1, l)
    e = lambda n, l: C(n, 2) * (tau + sig * l) * f(n - 2, l) + sig * C(n, 3) * (3 * f(n - 1, l) + 3 * f(n - 2, l) + f(n - 3, l))
    W = lambda s_, p, q, l, a: sum(C(n - p + q, q) * C(a, n) * s_(n, l) for n in range(max(p, 0), a + 1))
    up = lambda k, val: st.__setitem__(k, min(st.get(k, val), val))
    for l in range(N):
        for a in range(N + 1 - l):
            for n in range(1, a + 1):
                assert dif(b, n, l) == h(n, l) - v(n, l) - e(n, l), ('split', l, n)
            cc = c[l + 1]; B0 = W(phi, 2, 0, l, a)
            for j in range(1, N + 1):
                if a < 2 * j + 1: break
                fams = [('B', 1, lambda L, A, J: W(phi, 2 * J + 2, J, L, A)), ('H', 2, lambda L, A, J: W(h, 2 * J + 1, J, L, A)),
                        ('V', 2, lambda L, A, J: W(v, 2 * J + 1, J, L, A)), ('E', 2, lambda L, A, J: W(e, 2 * J + 1, J, L, A)),
                        ('C', 1, lambda L, A, J: W(f, 2 * J + 2, J + 1, L, A))]
                for name, jmin, Wf in fams:
                    if j < jmin: continue
                    Y = Wf(l, a, j)
                    if Y > 0: up('mu_' + name, B0 * (Wf(l + 1, a - 2, j - 1) if a >= 2 else 0) / (cc * Y))
                    elif Y < 0: up('neg_' + name, Y)
            if a >= 3:
                lhs = (b[l + a] - b[l]) * W(phi, 2, 0, l + 1, a - 1) + B0 * (b[l + a - 1] - b[l + 1])
                rhs = cc * (4 * W(h, 3, 1, l, a) - 2 * W(v, 3, 1, l, a) - W(e, 3, 1, l, a))
                if rhs > 0: up('key', lhs / rhs)
                elif lhs < 0: up('keyneg', lhs)
if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); u = F(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
    st = {}; tot = 0; t0 = time.time()
    for N in Ns:
        for _ in range(per):
            sg = lc_seq(rng, N)
            Dd = [sum(C(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]; d = [z / Dd[N] for z in Dd]
            r = F(rng.choice([1, 10, 50, 90, 99, 999])) / (1000 if rng.random() < .3 else 100); r = min(r, F(999, 1000))
            t1, tau1 = F(rng.choice([1, 1000])), F(rng.choice([1, 1000]))
            mk = lambda lam: (lam * t1, lam * tau1, u * lam * t1 * lam * tau1 / r)
            def okb(lam):
                t, tau, sg_ = mk(lam); rh = lambda z: r + t * z + tau * C(z, 2) + sg_ * C(z, 3)
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
