"""Weakened key (K'): A0(l,a) Y' + Y A0(l+1,a-2) >= D (4 H1 - g V1), with Y = sum_{n>=2} C(a,n) f_n(l),
Y' = sum_{n>=2} C(a-1,n) f_n(l+1), D = d_{l+1}, H1 = sum_{n>=3}(n-2)C(a,n)(1-rho(l+n)) f_n(l),
V1 = sum_{n>=3}(n-2)C(a,n) n Drho(l+n-1) f_{n-1}(l). Families: (G) arrays ('mix','steep','lin') and convex ratios that are
not Newton-log-concave ('cvx': random convex nondecreasing rho with b nondecreasing). Reports min ratio LHS/RHS per g.
Usage: key_weak.py Ns per seed fams"""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from g_ingredients import member
from hform import lc_seq

def cvx_member(rng, N, shape='cvx'):
    sg = lc_seq(rng, N)
    Dd = [sum(math.comb(n, k) * sg[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [z / Dd[N] for z in Dd]
    inc = [F(rng.randint(0, 20)) for _ in range(N)]
    if shape == 'cvx': inc = sorted(inc)                 # nondecreasing increments -> convex
    elif shape == 'ccv': inc = sorted(inc, reverse=True)  # concave nondecreasing
    g = [F(0)]
    for x in inc: g.append(g[-1] + x)
    r = F(rng.choice([1, 10, 50, 90, 99])) / 100
    def okb(k):
        rho = [r + k * x for x in g]; b = [(1 - p) * dd for p, dd in zip(rho, d)]
        return rho[-1] <= 1 and all(b[i + 1] >= b[i] for i in range(N))
    lo, hi = F(0), (1 - r) / (g[-1] if g[-1] else 1)
    for _ in range(30):
        mid = (lo + hi) / 2; lo, hi = (mid, hi) if okb(mid) else (lo, mid)
    k = lo * rng.choice([F(1), F(1, 2)])
    return d, [r + k * x for x in g]

def ratios(d, rv, gammas, stats, tag):
    N = len(d) - 1
    dif = lambda xs, n, l: sum((-1) ** (n - i) * math.comb(n, i) * xs[l + i] for i in range(n + 1)) if n >= 0 else F(0)
    b = [(1 - rv[i]) * d[i] for i in range(N + 1)]
    f = lambda n, l: dif(d, n, l)
    for l in range(N):
        for a in range(3, N + 1 - l):
            Y = sum(math.comb(a, n) * f(n, l) for n in range(2, a + 1))
            Yp = sum(math.comb(a - 1, n) * f(n, l + 1) for n in range(2, a))
            lhs = (b[l + a] - b[l]) * Yp + Y * (b[l + a - 1] - b[l + 1])
            H1 = sum((n - 2) * math.comb(a, n) * (1 - rv[l + n]) * f(n, l) for n in range(3, a + 1))
            V1 = sum((n - 2) * math.comb(a, n) * n * (rv[l + n] - rv[l + n - 1]) * f(n - 1, l) for n in range(3, a + 1))
            D = d[l + 1]
            for g in gammas:
                rhs = D * (4 * H1 - g * V1)
                if rhs > 0:
                    q = lhs / rhs; key = (tag, g)
                    if key not in stats or q < stats[key][0]: stats[key] = (q, l, a, N)

if __name__ == '__main__':
    Ns = [int(z) for z in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    fams = sys.argv[4].split(','); gammas = [F(0), F(2), F(8, 3)]; stats = {}
    for N in Ns:
        for it in range(per):
            fam = fams[it % len(fams)]
            if fam in ('cvx', 'ccv', 'mono'):
                d, rv = cvx_member(rng, N, fam)
            else:
                d, co = member(rng, N, fam)
                rv = [sum(ck * math.comb(x, k) for k, ck in enumerate(co) if k <= x) for x in range(N + 1)]
            ratios(d, rv, gammas, stats, fam)
    for k in sorted(stats, key=str): print(k[0], 'gamma', k[1], 'min ratio', float(stats[k][0]), 'at (l,a,N)', stats[k][1:])
