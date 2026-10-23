"""Proof ingredients for conjecture (G): ratio rho with nonnegative log-concave Newton coefficients (any degree),
log-concave Newton profile, b nondecreasing. psi_n = h_n - v_n - what_n with h = (1-rho(l+n)) f_n,
v = n Drho(l+n-1) f_{n-1} (j = 1) and what = sum_{j>=2} C(n,j) D^j rho(l+n-j) f_{n-j}. Reports minima over sources of:
lcphi = phi_2(l) phi_n(l+1) / (c phi_{n+2}(l))  [log-concavity inequality for phi, from (NP)],
mu_Y = B_0 Y_{j-1}' / (c Y_j) for Y = B, H, V, What, C (j as in the paper), and key ratios
(A0 B0' + B0 A0'') / (c (4 H1 - gV V1 - gW What1)). Usage: g_ingredients.py Ns per seed [fam]"""
import sys, math, random, time
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from hform import lc_seq

GAMMAS = {'(0,0)': (F(0), F(0)), '(4/3,0)': (F(4, 3), F(0)), '(2,0)': (F(2), F(0))}

def check(d, co, stats):
    N = len(d) - 1
    rhof = lambda x: sum(ck * math.comb(x, k) for k, ck in enumerate(co) if k <= x)
    rv = [rhof(i) for i in range(2 * N + 3)]
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    Dj = lambda j, x: dif(rv, j, x)
    c = [rv[i] * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]
    f = lambda n, l: dif(d, n, l); phi = lambda n, l: dif(c, n, l)
    h = lambda n, l: (1 - rv[l + n]) * f(n, l)
    v = lambda n, l: n * Dj(1, l + n - 1) * f(n - 1, l) if n >= 1 else F(0)
    wh = lambda n, l: sum(math.comb(n, j) * Dj(j, l + n - j) * f(n - j, l) for j in range(2, n + 1))
    W = lambda s, p, q, l, a: sum(math.comb(n - p + q, q) * math.comb(a, n) * s(n, l) for n in range(p, a + 1))
    upd = lambda k, val: stats.__setitem__(k, min(stats.get(k, val), val))
    for l in range(N):
        cc = c[l + 1]
        for n in range(1, N - l - 1):
            if phi(n + 2, l) > 0 and n >= 1: upd('lcphi', phi(2, l) * phi(n, l + 1) / (cc * phi(n + 2, l)))
        for a in range(N + 1 - l):
            for n in range(1, a + 1):
                assert dif(b, n, l) == h(n, l) - v(n, l) - wh(n, l), ('split', l, n)
            B0 = W(phi, 2, 0, l, a)
            for j in range(1, N + 1):
                if a < 2 * j + 1: break
                fams = [('B', 1, lambda L, A, J: W(phi, 2 * J + 2, J, L, A)), ('H', 2, lambda L, A, J: W(h, 2 * J + 1, J, L, A)),
                        ('V', 2, lambda L, A, J: W(v, 2 * J + 1, J, L, A)), ('What', 2, lambda L, A, J: W(wh, 2 * J + 1, J, L, A)),
                        ('C', 1, lambda L, A, J: W(f, 2 * J + 2, J + 1, L, A))]
                for name, jmin, Wf in fams:
                    if j < jmin: continue
                    Y = Wf(l, a, j)
                    if Y > 0: upd('mu_' + name, B0 * (Wf(l + 1, a - 2, j - 1) if a >= 2 else 0) / (cc * Y))
            if a >= 3:
                A0 = b[l + a] - b[l]; A0b = b[l + a - 1] - b[l + 1]
                lhs = A0 * W(phi, 2, 0, l + 1, a - 1) + B0 * A0b
                H1, V1, Wh1 = (W(s, 3, 1, l, a) for s in (h, v, wh))
                for gname, (gV, gW) in GAMMAS.items():
                    rhs = cc * (4 * H1 - gV * V1 - gW * Wh1)
                    if rhs > 0: upd('key' + gname, lhs / rhs)

def steep_member(rng, N):
    sg = lc_seq(rng, N)
    Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [z / Dd[N] for z in Dd]
    B = F(rng.choice([2, 3, 10, 100]))
    def okb(r):
        rh = lambda x: r * B ** x
        bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
        return rh(N) <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
    lo, hi = F(0), 1 / B ** N
    if okb(hi): lo = hi
    else:
        for _ in range(30):
            mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
    r = lo * rng.choice([F(1), F(1, 2)])
    return d, [r * (B - 1) ** k for k in range(N + 1)]

def member(rng, N, fam):
    if fam == 'steep': return steep_member(rng, N)
    if fam == 'lin':  # rho = r + t x at the largest t keeping b nondecreasing (or a fraction)
        sg = lc_seq(rng, N)
        Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
        d = [z / Dd[N] for z in Dd]
        r = F(rng.choice([1, 10, 30, 50, 80, 90, 95, 99])) / 100
        def okb(t):
            bb = [(1 - r - t * i) * d[i] for i in range(N + 1)]
            return r + t * N <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
        lo, hi = F(0), (1 - r) / N
        for _ in range(30):
            mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
        t = lo * rng.choice([F(1), F(1), F(1, 2)])
        return d, [r, t] + [F(0)] * (N - 1)
    sg = lc_seq(rng, N)
    Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [z / Dd[N] for z in Dd]
    r = F(rng.choice([1, 10, 30, 50, 80, 90, 95, 99])) / 100
    vs = sorted((F(rng.randint(0, 20), 20) for _ in range(N)), reverse=True)
    if fam == 'geo' or (fam == 'mix' and rng.random() < .3): vs = [F(1)] * N
    def cof(s):
        co = [r, s]
        for k in range(2, N + 1): co.append(co[-1] * (s / r) * vs[k - 2])
        return co
    def okb(s):
        co = cof(s); rh = lambda x: sum(ck * math.comb(x, k) for k, ck in enumerate(co) if k <= x)
        bb = [(1 - rh(i)) * d[i] for i in range(N + 1)]
        return rh(N) <= 1 and all(bb[i + 1] >= bb[i] for i in range(N))
    lo, hi = F(0), F(1)
    while okb(hi): hi *= 2
    for _ in range(30):
        mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
    return d, cof(lo * (F(rng.randint(1, 10), 10) if rng.random() < .4 else 1))

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    fam = sys.argv[4] if len(sys.argv) > 4 else 'mix'; stats = {}; t0 = time.time(); tot = 0
    for N in Ns:
        for _ in range(per):
            d, co = member(rng, N, fam); check(d, co, stats); tot += 1
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {tot} arrays, {time.time()-t0:.0f}s: " + ', '.join(f"{k}={float(v):.4g}" for k, v in sorted(stats.items())), flush=True)
