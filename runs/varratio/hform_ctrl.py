"""Controls for the h-form class: c = d LC-Newton, a = 1 - d; b chosen by mode.
modes: rand (b_n random in [0, s]), incr (b nondecreasing random), decr (b nonincreasing random),
       newton (b with nonnegative Newton coeffs, independent of sigma, not nec. LC), negnewton (some negative Newton coeffs)"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from hform import lc_seq
def member(rng, N, mode):
    sig = lc_seq(rng, N)
    D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]
    s = rng.choice([F(1, 100), F(1, 10), F(1), F(5)])
    R = lambda: s * F(rng.randint(0, 1000), 1000)
    if mode == 'rand': b = [R() for _ in range(N + 1)]
    elif mode == 'incr': b = sorted(R() for _ in range(N + 1))
    elif mode == 'decr': b = sorted((R() for _ in range(N + 1)), reverse=True)
    elif mode == 'newton':
        beta = [R() for _ in range(N + 1)]
        b = [sum(math.comb(n, k) * beta[k] for k in range(n + 1)) for n in range(N + 1)]
    return [1 - x for x in d], b, d
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3])); mode = sys.argv[4]
    tot = 0; fails = []
    for N in Ns:
        for _ in range(per):
            a, b, c = member(rng, N, mode)
            hit = first_negative(linearization(a, b, c)); tot += 1
            if hit: fails.append((N, hit[:3], float(hit[3]), [str(x) for x in b], [str(x) for x in c]))
    print(f'{mode}: {tot} members, {len(fails)} failures', flush=True)
    for f in fails[:3]: print(f)
