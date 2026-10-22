"""Exact check of the case proofs of (**'). V(x,y) = H_{k-1}(x,y) H_{k-1}(c1-s1-x, c2-s2-y), centre mu = (c-s)/2,
box B = [i0, c1-i0] x [j0, c2-j0]. Each ordered pair (e,e') is reduced to brackets claimed >= 0; we check every bracket
and that the brackets sum to the term V(B-e) - V(B). Also checks (T1) LC of windowed marginals, (T2) RR2 of V.
Usage: case_proofs.py Kmax"""
import sys
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def H(k, x, y): return C(k, x) * C(x, k - y) if k >= 0 and x >= 0 and y >= 0 else 0
Kmax = int(sys.argv[1]); fails = {}; checks = 0
def bad(name): fails[name] = fails.get(name, 0) + 1
for k in range(1, Kmax + 1):
    for c1 in range(0, 2 * k + 2):
        for c2 in range(0, 2 * k + 2):
            for s in [(2, 0), (0, 2), (1, 1), (2, 1), (1, 2), (2, 2)]:
                m1, m2 = c1 - s[0], c2 - s[1]
                V = lambda x, y: H(k - 1, x, y) * H(k - 1, m1 - x, m2 - y)
                R = lambda xs, ys: sum(V(x, y) for x in xs for y in ys)
                # (T2): RR2 on a window of points
                for x in range(-1, m1 + 2):
                    for xp in range(x + 1, m1 + 2):
                        for y in range(-1, m2 + 2):
                            for yp in range(y + 1, m2 + 2):
                                if V(x, y) * V(xp, yp) > V(x, yp) * V(xp, y): bad('RR2')
                for i0 in range(0, c1 // 2 + 1):
                    for j0 in range(0, c2 // 2 + 1):
                        I = range(i0, c1 - i0 + 1); J = range(j0, c2 - j0 + 1)
                        sh = lambda rg, d: range(rg.start + d, rg.stop + d)
                        term = lambda e: R(sh(I, -e[0]), sh(J, -e[1])) - R(I, J)
                        checks += 1
                        L = i0
                        if s == (2, 0):  # case ((1,0),(1,0)): G(L-1) - G(L-2), G centred window J
                            br = [R([L - 1], J) - R([L - 2], J)]
                            tot = term((1, 0)); name = 'axis'
                        elif s == (1, 1):  # case ((1,0),(0,1)): V(L-1, c2-j0) - V(L-1, j0-1)
                            br = [V(L - 1, c2 - j0) - V(L - 1, j0 - 1)]
                            tot = term((1, 0)); name = 'mixed'
                        elif s == (2, 1):  # case ((1,0),(1,1)) and ((1,1),(1,0))
                            br = [V(L - 1, c2 - j0) - V(L - 1, j0 - 1), R([L - 1], sh(J, -1)) - R([L - 2], sh(J, -1))]
                            tot = term((1, 0)); name = 'e10_e11'
                            zero = R(sh(I, -1), sh(J, -1)) - R(sh(I, -1), J)
                            if zero != 0: bad('e11_e10_zero_bracket')
                            if term((1, 1)) != zero + tot: bad('e11_e10_split')
                        elif s == (2, 2):  # case ((1,1),(1,1))
                            x1, x2 = i0 - 1, i0 - 2; Jm2 = sh(J, -2)
                            br = [R(sh(I, -1), [j0 - 1]) - R(sh(I, -1), [j0 - 2]),
                                  R([x1], J) - R([x1], Jm2), R([x1], Jm2) - R([x2], Jm2)]
                            tot = term((1, 1)); name = 'diag'
                        else:
                            continue
                        if sum(br) != tot: bad(name + '_sum')
                        for b in br:
                            if b < 0: bad(name + '_bracket')
                # (T1): LC of windowed marginals for all windows
                for lo in range(-1, m2 + 2):
                    for hi in range(lo, m2 + 2):
                        g = [R([x], range(lo, hi + 1)) for x in range(-1, m1 + 2)]
                        for t in range(1, len(g) - 1):
                            if g[t] ** 2 < g[t - 1] * g[t + 1]: bad('T1_LC')
print(f'{checks} (box, s) checks; failures: {fails if fails else "none"}')
