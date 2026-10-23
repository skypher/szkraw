"""Candidate B': Newton coefficients of b and of c (each) nonnegative and log-concave without internal zeros.
d = b + c scaled so d_N = 1; rho_N = c_N in (0,1]. a = 1 - d.
Exact full linearization tables (probe.linearization). Small N exhaustively random first, boundary rho_N near 1.
Usage: candB.py Ns per seed"""
import sys, math, random, time, threading
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..'))
from probe import linearization, first_negative
STATE = {'done': 0, 'msg': '', 't0': time.time()}
def _hb():
    while True:
        time.sleep(60)
        print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {STATE['done']} members, now {STATE['msg']}, elapsed {time.time()-STATE['t0']:.0f}s", flush=True)

def lc_seq(rng, n):
    """sigma_1..sigma_n >= 0, log-concave without internal zeros: s_1 * prod of nonincreasing quotients; random truncation."""
    mode = rng.random()
    top = rng.choice([F(1, 10), F(1, 2), F(1), F(3), F(10)])
    qs = sorted((top * F(rng.randint(0, 1000), 1000) for _ in range(n)), reverse=True)
    if mode < 0.2: qs = [F(0)] * n            # linear
    elif mode < 0.35: qs = [qs[0]] * n        # geometric
    K = rng.randint(1, n)
    out = [F(rng.randint(1, 100), 100)]
    for k in range(1, n):
        out.append(out[-1] * qs[k - 1] if k < K else F(0))
    return out

def newton(N, sig):
    return [F(0)] + [sum(math.comb(n, k) * sig[k - 1] for k in range(1, n + 1)) for n in range(1, N + 1)]

def member(rng, N):
    sb = lc_seq(rng, N) if rng.random() > 0.05 else [F(0)] * N
    sc = lc_seq(rng, N)
    B = newton(N, sb); C = newton(N, sc)
    u = rng.random()
    rhoN = F(rng.randint(1, 99), 100) if u < 0.6 else (1 - F(1, rng.choice([100, 1000, 10**4])) if u < 0.9 else F(1, rng.choice([100, 1000])))
    if B[N] == 0: rhoN = F(1)
    c = [x / C[N] * rhoN for x in C]
    b = [x / B[N] * (1 - rhoN) for x in B] if B[N] != 0 else [F(0)] * (N + 1)
    d = [x + y for x, y in zip(b, c)]
    if not all(d[n + 1] > d[n] for n in range(N)): return None
    a = [1 - x for x in d]
    return a, b, c

if __name__ == '__main__':
    threading.Thread(target=_hb, daemon=True).start()
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    tot = 0; fails = []
    for N in Ns:
        for _ in range(per):
            m = member(rng, N)
            if m is None: continue
            STATE['msg'] = f'N={N}'
            hit = first_negative(linearization(*m)); tot += 1; STATE['done'] += 1
            if hit:
                fails.append((N, hit[:3], float(hit[3]), [str(x) for x in m[1]], [str(x) for x in m[2]]))
        print(f'N={N}: cumulative {tot} members, {len(fails)} failures', flush=True)
    print(f"candidate B': {tot} members, {len(fails)} failures")
    for f in fails[:8]: print(f)
