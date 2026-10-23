"""Exact first-order test of (P) at r = 1 for constant-ratio arrays a = 1 - d, b = (1-r) d, c = r d.
With r = 1 - eta, every coefficient is g = g0 + eta g1 + O(eta^2) (g is a polynomial in r: the recurrence divides
only by a_m = 1 - d_m). (P) fails for all small eta > 0 if some g0 < 0, or g0 = 0 and g1 < 0.
fails_near1(d) returns (kind, m, n, k, value) of the worst entry or None. Also: full_table(d, r) exact at a given r."""
from fractions import Fraction as F
from math import comb
def profile(sig, N):
    D = [sum(comb(i, k) * sig[k - 1] for k in range(1, min(i, len(sig)) + 1)) for i in range(N + 1)]
    return [x / D[N] for x in D]
def tables_dual(d):
    N = len(d) - 1; size = N + 1
    a = [1 - x for x in d]
    # b = eta d, c = d - eta d : dual pairs (value, eta-coefficient)
    b = [(F(0), x) for x in d]; c = [(x, -x) for x in d]
    Z = (F(0), F(0))
    cur = [[(F(int(i == j)), F(0)) for j in range(size)] for i in range(size)]
    prev = [[Z] * size for _ in range(size)]
    out = [cur]
    for m in range(N):
        nxt = []
        am = a[m]
        for i in range(size):
            row = []
            bi_bm = (F(0), b[i][1] - b[m][1])
            for j in range(size):
                cv, ce = cur[i][j]; pv, pe = prev[i][j]
                v = -c[m][0] * pv; e = -(c[m][0] * pe + c[m][1] * pv)
                e += bi_bm[1] * cv
                if i:
                    xv, xe = cur[i - 1][j]; v += c[i][0] * xv; e += c[i][0] * xe + c[i][1] * xv
                if i < N:
                    xv, xe = cur[i + 1][j]; v += a[i] * xv; e += a[i] * xe
                row.append((v / am, e / am))
            nxt.append(row)
        prev, cur = cur, nxt
        out.append(cur)
    return out
def fails_near1(d):
    T = tables_dual(d); worst = None
    for m, M in enumerate(T):
        for n, row in enumerate(M):
            for k, (v, e) in enumerate(row):
                if v < 0: cand = ('g0<0', m, n, k, v)
                elif v == 0 and e < 0: cand = ('g1<0', m, n, k, e)
                else: continue
                if worst is None or cand[0] < worst[0] or (cand[0] == worst[0] and cand[4] < worst[4]): worst = cand
    return worst
if __name__ == '__main__':
    import sys
    # sanity: Krawtchouk and geometric profiles must pass (Theorem 2.1)
    for N in (3, 4, 5, 6, 7):
        for q in (F(1), F(2), F(1, 3)):
            sig = [q ** k for k in range(N)] if q != 1 else [F(1)] + [F(0)] * (N - 1)
            print(N, q, fails_near1(profile(sig, N)))
