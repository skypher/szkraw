"""Class (Q): worst per-term ratio c_{l+1} phi_{n+2}(l) / (phi_2(l) phi_n(l+1)), n >= 2, l + n + 2 <= N.
The B-detour needs <= 5/4 (coefficient ratio >= 5 vs 4); <= 1 would be the Lemma 8.3 analogue.
Profiles: random LC Newton (lc_seq), geometric Newton ratio q, quadratic; (t, tau) up to equality in the
monotonicity condition. Usage: bdetour_ratio.py Ns per seed"""
import sys, math, random
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from hform import lc_seq
def run(d, r, t, tau):
    N = len(d) - 1
    rho = lambda x: r + t * x + tau * F(x * (x - 1), 2)
    c = [rho(i) * d[i] for i in range(N + 1)]
    dif = lambda x, n, l: sum((-1) ** (n - i) * math.comb(n, i) * x[l + i] for i in range(n + 1))
    worst = (F(0), None)
    for l in range(N + 1):
        for n in range(2, N + 1):
            if l + n + 2 > N: break
            num = c[l + 1] * dif(c, n + 2, l); den = dif(c, 2, l) * dif(c, n, l + 1)
            if den > 0 and num / den > worst[0]: worst = (num / den, (l, n))
            if den == 0 and num > 0: worst = (F(10 ** 9), (l, n))
    return worst
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    W = (F(0),)
    for N in Ns:
        for k in range(per):
            mode = k % 3
            if mode == 0: sig = lc_seq(rng, N)
            elif mode == 1:
                q = F(rng.choice([1, 2, 5, 10, 50]), rng.choice([1, 10, 100])); sig = [q ** j for j in range(N)]
            else: sig = [F(1), F(rng.randint(0, 20), rng.choice([1, 10]))] + [F(0)] * (N - 2)
            D = [sum(math.comb(n, j) * sig[j - 1] for j in range(1, n + 1)) for n in range(N + 1)]
            d = [x / D[N] for x in D]
            r = F(rng.randint(1, 19), 20); R = d[N - 1] / (1 - d[N - 1])
            lam = F(rng.randint(0, 10), 10)  # share of the budget on t
            budget = 1 - r
            t = lam * budget / (N + R); tau = (1 - lam) * budget / (F(N * (N - 1), 2) + (N - 1) * R)
            w = run(d, r, t, tau)
            if w[0] > W[0]: W = (w[0], N, mode, float(r), float(lam), w[1])
        print(N, 'worst ratio so far', float(W[0]), W[1:], flush=True)
