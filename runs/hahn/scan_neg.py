"""Hahn and dual Hahn on the second positive branch (parameters < -N),
which contains the Johnson-scheme parameters."""
from fractions import Fraction as F
from itertools import product
from families import hahn, dual_hahn, normalize
from criteria import check_all, min_g
KEYS = ["P1", "P2_A", "P2_quadratic", "P2_cubic", "P2_vary", "P2_quadarray", "P2_lowdeg"]
for N in (4, 6):
    G = [F(-N) - F(1, 2), F(-N - 1), F(-N - 2), F(-2 * N), F(-3 * N), F(-N - 20)]
    for fam, f in (("hahn", hahn), ("dual_hahn", dual_hahn)):
        tally = {}
        for x, y in product(G, G):
            try:
                X, P = f(N, x, y)
            except ZeroDivisionError:
                continue
            for e in (0, N):
                try:
                    arr = normalize(X, P, e)
                except (ValueError, ZeroDivisionError, StopIteration):
                    arr = None
                if arr is None:
                    continue
                r = check_all(*arr)
                if not r["stoch"]:
                    continue
                k = ("P" if min_g(*arr) >= 0 else "-", "proflc" if r["profile_lc"] else "notlc",
                     "cov" if any(r[q] for q in KEYS) else "nocov")
                tally[k] = tally.get(k, 0) + 1
        print(N, fam, tally)
