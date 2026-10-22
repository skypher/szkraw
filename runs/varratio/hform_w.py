"""h-form: c = d LC-Newton (sigma), a = 1 - d, b Newton coeffs beta_0 >= 0, beta_k = w_k sigma_k.
wmode: rand (w_k random >= 0), geo (w_k = W^k, W in {2,5,20}), spike (one w_k large)"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from hform import lc_seq
def member(rng, N, wmode):
    sig = lc_seq(rng, N)
    D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]; s = [x / D[N] for x in sig]
    sc = rng.choice([F(1, 100), F(1, 10), F(1), F(5)])
    if wmode == 'rand': ws = [sc * F(rng.randint(0, 1000), 1000) for _ in range(N)]
    elif wmode == 'geo':
        W = rng.choice([2, 5, 20]); ws = [sc * F(W) ** k for k in range(N)]
    else:
        ws = [sc * F(rng.randint(0, 100), 1000) for _ in range(N)]; ws[rng.randrange(N)] = sc * 50
    beta0 = rng.choice([F(0), sc * F(rng.randint(0, 1000), 1000)])
    beta = [beta0] + [w * x for w, x in zip(ws, s)]
    b = [sum(math.comb(n, k) * beta[k] for k in range(n + 1)) for n in range(N + 1)]
    return [1 - x for x in d], b, d
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3])); wm = sys.argv[4]
    tot = 0; fails = []
    for N in Ns:
        for _ in range(per):
            a, b, c = member(rng, N, wm)
            hit = first_negative(linearization(a, b, c)); tot += 1
            if hit: fails.append((N, hit[:3], float(hit[3]), [str(x) for x in b], [str(x) for x in c]))
    print(f'{wm}: {tot} members, {len(fails)} failures', flush=True)
    for f in fails[:3]: print(f)
