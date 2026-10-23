"""Exact check of all coefficients g(m,N;k) (one index equal to N) via v_{m+1} = (v_m J - b_m v_m - c_m v_{m-1})/a_m,
v_0 = e_N, where v_m = row N of R_m(J). Families: rho_n = r + kappa*g(n/N) on profiles with geometric increments q.
kappa = lam * kappa_max (b nondecreasing, rho_N <= 1). Usage: rowN_probe.py Ns families qs rs lams"""
import sys, time, threading
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from nonlinear_probe import profile, gfun, kappa_max

def rowN(a, b, c):
    N = len(a) - 1
    v_prev = None
    v = [F(0)] * N + [F(1)]
    worst = (None, None, F(0))
    for m in range(N):
        vJ = [(v[j + 1] * c[j + 1] if j < N else 0) + v[j] * b[j] + (v[j - 1] * a[j - 1] if j > 0 else 0) for j in range(N + 1)]
        nxt = [(vJ[j] - b[m] * v[j] - (c[m] * v_prev[j] if v_prev is not None else 0)) / a[m] for j in range(N + 1)]
        v_prev, v = v, nxt
        for k, x in enumerate(v):
            if x < worst[2]: worst = (m + 1, k, x)
    return worst

if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1].split(',')]; fams = sys.argv[2].split(',')
    qs = [x if x[0] in 'pc' else F(x) for x in sys.argv[3].split(',')]; rs = [F(x) for x in sys.argv[4].split(',')]
    lams = [F(x) for x in sys.argv[5].split(',')]
    t0 = time.time(); cnt = 0; neg = 0
    total = len(Ns) * len(qs) * len(fams) * len(rs) * len(lams)
    CUR = {'item': ''}
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
                for r in rs:
                    km = kappa_max(d, g, r)
                    for lam in lams:
                        k = km * lam
                        CUR['item'] = f"N={N} q={q} {name} r={r} lam={lam}"
                        c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                        b = [dn - cn for dn, cn in zip(d, c)]
                        a = [1 - dn for dn in d]
                        m, kk, x = rowN(a, b, c); cnt += 1
                        if x < 0:
                            neg += 1
                            print(f"NEG N={N} q={q} {name} r={r} lam={lam} kappa={float(k):.5f} g({m},{N};{kk})={float(x):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done, {cnt} arrays, {neg} negative, {time.time()-t0:.0f}s", flush=True)
