"""Varying-ratio candidate in the normalization a_n + c_n = 1 (h-form).
c_n = d_n with Newton coefficients sigma_k >= 0 log-concave (no internal zeros), d_N = 1; a_n = 1 - d_n.
b_n = sum_k C(n,k) beta_k with beta_0 >= 0 and beta_k = w_k sigma_k (k >= 1), w nonincreasing >= 0.
Constant ratio (Theorem 8.1) is beta_0 = 0, w constant. Exact full linearization tables.
Usage: hform.py Ns per seed [mode]   mode: M (w nonincreasing, default) | inc (w nondecreasing, control)"""
import sys, math, random, time, threading
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw')
from probe import linearization, first_negative
STATE = {'done': 0, 'msg': '', 't0': time.time()}
def _hb():
    while True:
        time.sleep(60)
        print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {STATE['done']} members, now {STATE['msg']}, elapsed {time.time()-STATE['t0']:.0f}s", flush=True)

def lc_seq(rng, n):
    mode = rng.random()
    top = rng.choice([F(1, 10), F(1, 2), F(1), F(3), F(10)])
    qs = sorted((top * F(rng.randint(0, 1000), 1000) for _ in range(n)), reverse=True)
    if mode < 0.2: qs = [F(0)] * n
    elif mode < 0.35: qs = [qs[0]] * n
    K = rng.randint(1, n)
    out = [F(1)]
    for k in range(1, n):
        out.append(out[-1] * qs[k - 1] if k < K else F(0))
    return out

def member(rng, N, mode):
    sig = lc_seq(rng, N)
    D = [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    d = [x / D[N] for x in D]
    s = [x / D[N] for x in sig]               # Newton coefficients of d
    scale = rng.choice([F(1, 100), F(1, 10), F(1), F(5), F(50)])
    ws = sorted((scale * F(rng.randint(0, 1000), 1000) for _ in range(N)), reverse=(mode == 'M'))
    if rng.random() < 0.2: ws = [ws[0]] * N
    beta0 = rng.choice([F(0), F(0), scale * F(rng.randint(0, 1000), 1000)])
    beta = [beta0] + [w * x for w, x in zip(ws, s)]
    b = [sum(math.comb(n, k) * beta[k] for k in range(0, n + 1)) for n in range(N + 1)]
    return [1 - x for x in d], b, d

if __name__ == '__main__':
    threading.Thread(target=_hb, daemon=True).start()
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    mode = sys.argv[4] if len(sys.argv) > 4 else 'M'
    tot = 0; fails = []
    for N in Ns:
        for _ in range(per):
            a, b, c = member(rng, N, mode)
            STATE['msg'] = f'N={N}'
            hit = first_negative(linearization(a, b, c)); tot += 1; STATE['done'] += 1
            if hit: fails.append((N, hit[:3], float(hit[3]), [str(x) for x in b], [str(x) for x in c]))
        print(f'N={N}: cumulative {tot}, failures {len(fails)}', flush=True)
    print(f'mode {mode}: {tot} members, {len(fails)} failures')
    for f in fails[:6]: print(f)
