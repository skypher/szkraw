"""(G) in the far-field regime: geometric profile d_i = ((1+w)^i - 1)/((1+w)^N - 1) with l*w >> 1 reachable (N large),
ratios on the LC boundary rho = r + t x + (t^2/r) C(x,2) and exponential rho = r B^x, t (or r) = lam * max with b
nondecreasing. Checks the rows g(m,N;k) exactly. Heartbeat every 60 s. Usage: g_farfield.py Ns ws rs lams"""
import sys, math, time, threading
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from rowN_probe import rowN
CUR = {'item': '', 'done': 0, 'total': 0}; t0 = time.time()
def hb():
    while True:
        time.sleep(60)
        print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {CUR['done']}/{CUR['total']} arrays, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
threading.Thread(target=hb, daemon=True).start()
Ns = [int(z) for z in sys.argv[1].split(',')]; ws = [F(z) for z in sys.argv[2].split(',')]
rs = [F(z) for z in sys.argv[3].split(',')]; lams = [F(z) for z in sys.argv[4].split(',')]
CUR['total'] = len(Ns) * len(ws) * len(rs) * len(lams) * 2
for N in Ns:
    for w in ws:
        q = 1 + w; D = q ** N - 1
        d = [(q ** i - 1) / D for i in range(N + 1)]
        for r in rs:
            for fam in ['lcquad', 'exp']:
                def rho_of(p):
                    if fam == 'lcquad': return lambda x: r + p * x + (p * p / r) * F(x * (x - 1), 2)
                    return lambda x: r * (1 + p) ** x
                def ok(p):
                    rh = rho_of(p)
                    if rh(N) > 1: return False
                    prev = F(0)
                    for i in range(1, N + 1):
                        bi = (1 - rh(i)) * d[i]
                        if bi < prev: return False
                        prev = bi
                    return True
                lo, hi = F(0), F(1)
                for _ in range(24):
                    mid = (lo + hi) / 2; lo, hi = (mid, hi) if ok(mid) else (lo, mid)
                for lam in lams:
                    CUR['item'] = f'N={N} w={w} r={r} {fam} lam={lam}'
                    rh = rho_of(lo * lam)
                    c = [rh(i) * d[i] for i in range(N + 1)]; b = [d[i] - c[i] for i in range(N + 1)]; a_ = [1 - x for x in d]
                    m, k, v = rowN(a_, b, c); CUR['done'] += 1
                    print(f"[{time.strftime('%H:%M:%S')}] N={N} w={w} r={r} {fam} lam={lam} p={float(lo*lam):.3g}: rows min {float(v):.3e} at g({m},{N};{k}) -> {'OK' if v >= 0 else 'FAIL'}", flush=True)
