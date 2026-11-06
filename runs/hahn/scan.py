"""Scan finite classical families: where does property (P) hold, and which
P1/P2 criterion certifies it?  Exact arithmetic throughout."""
import sys, time
from fractions import Fraction as F
from itertools import product
from families import *
from criteria import *

KEYS = ["P1", "P2_A", "P2_quadratic", "P2_cubic", "P2_vary", "P2_quadarray", "P2_lowdeg"]
G = [F(-1, 2), F(0), F(1, 2), F(1), F(2), F(5), F(20)]
Qs = [F(1, 3), F(1, 2), F(4, 5), F(5, 4), F(2), F(3)]
Ps = [F(-5), F(-1, 2), F(1, 10), F(1, 3), F(1, 2), F(2, 3), F(2), F(10)]

def configs(fam, N):
    if fam == "hahn":
        for al, be in product(G, G):
            yield (al, be), hahn(N, al, be)
    elif fam == "dual_hahn":
        for ga, de in product(G, G):
            yield (ga, de), dual_hahn(N, ga, de)
    elif fam == "racah":
        for be, ga, de in product([F(-N - 5), F(-N - 3, 2) - 1, F(1, 2), F(2), F(N + 4)],
                                  [F(-1, 2), F(1), F(4), F(-N - 3)], [F(-1, 2), F(1), F(4), F(-N - 3)]):
            try:
                yield (be, ga, de), racah(N, be, ga, de)
            except ZeroDivisionError:
                pass
    elif fam in ("q_krawtchouk", "quantum_q_krawtchouk", "affine_q_krawtchouk", "dual_q_krawtchouk"):
        f = globals()[fam]
        for p, q in product(Ps, Qs):
            try:
                yield (p, q), f(N, p, q)
            except ZeroDivisionError:
                pass
    elif fam in ("q_hahn", "dual_q_hahn"):
        f = globals()[fam]
        for x, y, q in product([F(1, 4), F(1, 2), F(2), F(-1, 2)], [F(1, 4), F(1, 2), F(2), F(-1, 2)], Qs):
            try:
                yield (x, y, q), f(N, x, y, q)
            except ZeroDivisionError:
                pass

fam = sys.argv[1]
Ns = [int(v) for v in sys.argv[2].split(",")]
out = open(f"scan_{fam}.txt", "w")
stats = {}
t0 = time.time()
for N in Ns:
    for par, (X, P) in configs(fam, N):
        for e in (0, N):
            try:
                arr = normalize(X, P, e)
            except (ValueError, ZeroDivisionError, StopIteration):
                arr = None
            if arr is None:
                continue
            a, b, c = arr
            r = check_all(a, b, c)
            if not r["stoch"]:
                continue
            g = min_g(a, b, c)
            tag = "P" if g >= 0 else "-"
            cov = [k for k in KEYS if r[k]]
            key = (N, tag, "cov" if cov else "nocov", "const" if r["const_ratio"] else "vary")
            stats[key] = stats.get(key, 0) + 1
            out.write(f"N={N} par={tuple(str(v) for v in par)} e={e} P={tag} ming={float(g):.3g} "
                      f"const={r['const_ratio']} proflc={r['profile_lc']} bnd={r['b_nondecr']} cov={cov}\n")
            if cov and g < 0:
                print("!!! criterion claims P but g<0", N, par, e, cov, float(g))
    print(f"[{time.strftime('%H:%M:%S')}] {fam} N={N} done ({time.time()-t0:.0f}s)", flush=True)
for k in sorted(stats):
    print(fam, k, stats[k])
