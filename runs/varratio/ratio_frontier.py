"""Locate the frontier of property (P) for increasing ratios rho_n = r + kappa*g(n) beyond the quadratic case.
Families g: powers (n/N)^k and exponentials B^(n-N). Profiles: linear (q=1) and geometric increments q.
kappa = lam * kappa_max (b nondecreasing, rho_N <= 1), as in nonlinear_probe.py. Full linearization table
(exact). Prints each failure and, at the end, the smallest failing N per (family, r).
Usage: ratio_frontier.py Nmin Nmax families rs qs lams"""
import sys, time, threading
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw')
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from nonlinear_probe import profile, kappa_max

def gfun(name, N):
    if name.startswith('pow'):
        k = int(name[3:]); return [F(n ** k, N ** k) for n in range(N + 1)]
    if name.startswith('exp'):
        B = F(name[3:].replace('_', '/')); return [B ** n / B ** N for n in range(N + 1)]
    if name.startswith('c3'):  # pure cubic Newton term C(x,3)/C(N,3); 'c3t' adds equal weights on x and C(x,2)
        from math import comb
        g = [F(comb(n, 3)) + (F(n) * comb(N, 3) / N + F(comb(n, 2)) * comb(N, 3) / comb(N, 2) if name == 'c3t' else 0)
             for n in range(N + 1)]
        return [v / g[N] for v in g] if g[N] else None
    if name.startswith('top'):  # ratio raised only on the last k indices: g = 1 there
        k = int(name[3:]); return [F(1) if n > N - k else F(0) for n in range(N + 1)]
    if name.startswith('h'):  # second difference of rho prescribed: g(x) = sum_{y<x} sum_{z<y} h(z), normalized
        kind, m = name[1:].split('_') if '_' in name else (name[1:], '2')
        M = max(1, (N * int(m)) // 4)
        hz = {'lin': lambda z: F(z + 1), 'min': lambda z: F(min(z + 1, M)), 'sat': lambda z: 1 - F(1, 2 ** (z + 1)),
              'rat': lambda z: F(z + 1, z + 1 + M), 'inv': lambda z: F(1, z + 1), 'geo': lambda z: F(1, 2 ** z),
              'dec': lambda z: F(max(M - z, 0)), 'step': lambda z: F(1 if z >= M else 0),
              'const': lambda z: F(1)}[kind]
        g = [F(0)] * (N + 1)
        for x in range(2, N + 1): g[x] = g[x - 1] + sum(hz(z) for z in range(x - 1))
        return [v / g[N] for v in g] if g[N] else None  # None: family empty at this N
    raise ValueError(name)

if __name__ == '__main__':
    Nmin, Nmax = int(sys.argv[1]), int(sys.argv[2])
    fams = sys.argv[3].split(','); rs = [F(x) for x in sys.argv[4].split(',')]
    qs = [x if x[0] in 'pc' else F(x) for x in sys.argv[5].split(',')]; lams = [F(x) for x in sys.argv[6].split(',')]
    total = (Nmax - Nmin + 1) * len(fams) * len(rs) * len(qs) * len(lams)
    t0 = time.time(); cnt = 0; neg = 0; first = {}; CUR = {'item': ''}
    def _hb():
        while True:
            time.sleep(30)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {cnt}/{total} arrays, {neg} negative, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for N in range(Nmin, Nmax + 1):
        tN = time.time()
        for q in qs:
            d = profile(N, q)
            for name in fams:
                g = gfun(name, N)
                if g is None: continue
                for r in rs:
                    km = kappa_max(d, g, r)
                    for lam in lams:
                        CUR['item'] = f"N={N} q={q} {name} r={r} lam={lam}"
                        k = km * lam
                        c = [(r + k * gn) * dn for gn, dn in zip(g, d)]
                        b = [dn - cn for dn, cn in zip(d, c)]
                        a = [1 - dn for dn in d]
                        x = first_negative(linearization(a, b, c)); cnt += 1
                        if x:
                            neg += 1; first.setdefault((name, r, q), N)
                            print(f"NEG N={N} q={q} {name} r={r} lam={lam} kappa={float(k):.4g} at {x[:3]} val={float(x[3]):.3e}", flush=True)
        print(f"[{time.strftime('%H:%M:%S')}] N={N} done in {time.time()-tN:.1f}s, {cnt}/{total} arrays, {neg} negative", flush=True)
    print("smallest failing N per (family, r, q):", flush=True)
    for key in sorted(first, key=str): print(f"  {key[0]} r={key[1]} q={key[2]}: N={first[key]}", flush=True)
