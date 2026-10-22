"""Quadratic arrays: b_n = beta1 n + beta2 C(n,2), c_n = kappa1 n + kappa2 C(n,2) (b_0 = c_0 = 0), scaled to b_N + c_N = 1,
a = 1 - b - c. Claim: kappa2 >= 0 (c convex), beta2 + kappa2 >= 0 (d = b + c convex), b nondecreasing => (P).
Controls drop one condition at a time. Exact full tables."""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw')
from probe import linearization, first_negative

def build(N, b1, b2, k1, k2):
    B = [b1 * n + b2 * math.comb(n, 2) for n in range(N + 1)]
    C = [k1 * n + k2 * math.comb(n, 2) for n in range(N + 1)]
    s = B[N] + C[N]
    if s <= 0: return None
    b = [x / s for x in B]; c = [x / s for x in C]; a = [1 - x - y for x, y in zip(b, c)]
    if any(x <= 0 for x in c[1:]) or any(x <= 0 for x in a[:N]) or any(x < 0 for x in b): return None
    return a, b, c

def rnd(rng, lo, hi): return F(rng.randint(int(lo * 1000), int(hi * 1000)), 1000)

def sample(rng, N, mode):
    for _ in range(500):
        k1 = rnd(rng, 0.01, 1); k2 = rnd(rng, -0.3, 0.3); b1 = rnd(rng, 0, 1); b2 = rnd(rng, -0.3, 0.3)
        if rng.random() < 0.2: b1 = rnd(rng, 0, 0.01)
        m = build(N, b1, b2, k1, k2)
        if m is None: continue
        a, b, c = m
        cconv = k2 >= 0; dconv = b2 + k2 >= 0; bmono = all(b[i + 1] >= b[i] for i in range(N))
        conds = {'all': cconv and dconv and bmono,
                 'no_cconv': (not cconv) and dconv and bmono,
                 'no_dconv': cconv and (not dconv) and bmono,
                 'no_bmono': cconv and dconv and (not bmono)}
        if conds[mode]: return m
    return None

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[3])); Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2])
    for mode in ('all', 'no_cconv', 'no_dconv', 'no_bmono'):
        tot = fails = 0; ex = None
        for N in Ns:
            for _ in range(per):
                m = sample(rng, N, mode)
                if m is None: continue
                tot += 1
                hit = first_negative(linearization(*m))
                if hit:
                    fails += 1
                    if ex is None: ex = (N, hit[:3], float(hit[3]))
        print(f'{mode}: {tot} members, {fails} with a negative coefficient', ex if ex else '', flush=True)
