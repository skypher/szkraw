"""Exact check of the proof ingredients for ratios rho(x) = r + t x + tau C(x,2) (t, tau >= 0), b nondecreasing:
psi_n = h_n - v_n - w_n with h_n = (1-rho(l+n)) f_n, v_n = n (t + tau (l+n-1)) f_{n-1}, w_n = C(n,2) tau f_{n-2};
(i) Newton(c) log-concave without internal zeros; (ii) split identity; (iii) detours on Omega:
4c B_j <= B_0 B_{j-1}', 4c H_j <= B_0 H_{j-1}', 4c V_j <= B_0 V_{j-1}', 2c W_j <= B_0 W_{j-1}' (j>=2), 4c C'_j <= B_0 C'_{j-1}';
(iv) key: A_0 B_0(l+1,a-1) + B_0 A_0(l+1,a-2) >= c (4 H_1 - 2 V_1), a >= 3. Usage: quad_ingredients.py Ns per seed"""
import sys, math, random, time
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq

def check(d, r, t, tau):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
    c = [rho(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    f = lambda n, l: dif(d, n, l) if n >= 0 else F(0)
    h = lambda n, l: (1 - rho(l + n)) * f(n, l)
    v = lambda n, l: n * (t + tau * (l + n - 1)) * f(n - 1, l)
    w = lambda n, l: math.comb(n, 2) * tau * f(n - 2, l)
    fc = lambda n, l: dif(c, n, l); fb = lambda n, l: dif(b, n, l)
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    bad = []
    kap = [dif(c, k, 0) for k in range(N + 1)]
    for k in range(2, N):
        if kap[k] ** 2 < kap[k - 1] * kap[k + 1]: bad.append(('LC', k))
    pos = [k for k in range(1, N + 1) if kap[k] > 0]
    if any(kap[k] < 0 for k in range(1, N + 1)) or (pos and pos != list(range(pos[0], pos[-1] + 1))): bad.append(('supp',))
    for l in range(N + 1):
        for a in range(N + 1 - l):
            for n in range(1, a + 1):
                if fb(n, l) != h(n, l) - v(n, l) - w(n, l): bad.append(('split', l, n))
            cc = c[l + 1] if l + 1 <= N else None
            if cc is None: continue
            B0 = W(fc, 2, 0, l, a)
            for j in range(1, N + 1):
                if a < 2 * j + 1: break
                pairs = [('B', 4, lambda L, A, J: W(fc, 2 * J + 2, J, L, A)), ('H', 4, lambda L, A, J: W(h, 2 * J + 1, J, L, A)),
                         ('V', 4, lambda L, A, J: W(v, 2 * J + 1, J, L, A)), ('W', 2, lambda L, A, J: W(w, 2 * J + 1, J, L, A)),
                         ('C', 4, lambda L, A, J: W(lambda n, ll: dif(d, n, ll), 2 * J + 2, J + 1, L, A))]
                for name, mu, Wf in pairs:
                    if name in ('H', 'V', 'W') and j < 2: continue
                    lhs = mu * cc * Wf(l, a, j); rhs = B0 * (Wf(l + 1, a - 2, j - 1) if a >= 2 else 0)
                    if lhs > rhs: bad.append((name, l, a, j, float(lhs - rhs)))
            if a >= 3:
                A0 = b[l + a] - b[l]; A0b = b[l + a - 1] - b[l + 1]
                lhs = A0 * W(fc, 2, 0, l + 1, a - 1) + B0 * A0b
                rhs = cc * (4 * W(h, 3, 1, l, a) - 2 * W(v, 3, 1, l, a))
                if lhs < rhs: bad.append(('key', l, a, float(lhs - rhs)))
    return bad

if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    t0 = time.time(); tot = 0; nbad = {}
    for N in Ns:
        for _ in range(per):
            sig = lc_seq(rng, N)
            D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
            d = [x / D[N] for x in D]
            r = F(rng.randint(1, 19), 20); al = F(rng.randint(0, 10), 10)
            # rho = r + kap*(al x/N + (1-al) x^2/N^2), x^2 = 2C(x,2) + x
            def mk(kap): return kap * (al / N + (1 - al) / N ** 2), 2 * kap * (1 - al) / N ** 2
            def okb(kap):
                t, tau = mk(kap); rh = lambda x: r + t * x + tau * F(x * (x - 1), 2)
                bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
                return all(bb[i + 1] >= bb[i] for i in range(N))
            lo, hi = F(0), (1 - r)
            for _ in range(25):
                mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
            kap = lo * (F(rng.randint(1, 10), 10) if rng.random() < .5 else 1)
            t, tau = mk(kap)
            bad = check(d, r, t, tau); tot += 1
            for x in bad: nbad[x[0]] = nbad.get(x[0], 0) + 1
            if bad: print(f"N={N} r={r} al={al} kap={float(kap):.4f} bad={bad[:4]}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {tot} arrays, failures by kind {nbad}, {time.time()-t0:.0f}s", flush=True)
