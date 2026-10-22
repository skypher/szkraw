"""Row-N exact scan (all g(m,N;k)) for the power and exponential ratio families of ratio_frontier.py at larger N.
Usage: rowN_frontier.py Ns families qs rs lams"""
import sys, time, threading
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from nonlinear_probe import profile, kappa_max
from rowN_probe import rowN
from ratio_frontier import gfun

if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; fams = sys.argv[2].split(',')
    qs = [x if x[0] in 'pc' else F(x) for x in sys.argv[3].split(',')]; rs = [F(x) for x in sys.argv[4].split(',')]
    lams = [F(x) for x in sys.argv[5].split(',')]
    t0 = time.time(); cnt = 0; neg = 0; CUR = {'item': ''}
    total = len(Ns) * len(qs) * len(fams) * len(rs) * len(lams)
    def _hb():
        while True:
            time.sleep(60)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} negative, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in Ns:
        for q in qs:
            d = profile(N, q)
            for name in fams:
                g = gfun(name, N)
                if g is None: continue
                for r in rs:
                    km = kappa_max(d, g, r)
                    for lam in lams:
                        k = km * lam; CUR['item'] = f"N={N} q={q} {name} r={r} lam={lam}"
                        c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                        b = [dn - cn for dn, cn in zip(d, c)]
                        a = [1 - dn for dn in d]
                        m, kk, x = rowN(a, b, c); cnt += 1
                        if x < 0:
                            neg += 1
                            print(f"NEG N={N} q={q} {name} r={r} lam={lam} kappa={float(k):.5g} g({m},{N};{kk})={float(x):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {cnt}/{total} arrays, {neg} negative, {time.time()-t0:.0f}s", flush=True)
