"""Flow proof of (**'): D(B) = sum_e sum_{a' in Out_e} [H_k(a')H_{k-1}(b) - H_{k-1}(a')H_k(b)], b = c - a' - e,
Out_e = {a' in B : a' + e not in B}. Checks (1) the identity against the direct box sum, (2) termwise signs, and (3) signs
after grouping the terms by boundary point a' (summing over e). Usage: flow_terms.py Kmax"""
import sys
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def H(k, p):
    i, j = p
    return C(k, i) * C(i, k - j) if k >= 0 and i >= 0 and j >= 0 else 0
E = [(1, 0), (0, 1), (1, 1)]
Kmax = int(sys.argv[1]); ident_bad = 0; term_neg = 0; point_neg = 0; boxes = 0; terms = 0
for k in range(1, Kmax + 1):
    for c1 in range(0, 2 * k + 2):
        for c2 in range(0, 2 * k + 2):
            for i0 in range(0, c1 // 2 + 1):
                for j0 in range(0, c2 // 2 + 1):
                    inB = lambda p: i0 <= p[0] <= c1 - i0 and j0 <= p[1] <= c2 - j0
                    direct = sum(H(k, (i, j)) * H(k, (c1 - i, c2 - j)) - H(k - 1, (i, j)) * H(k + 1, (c1 - i, c2 - j))
                                 for i in range(i0, c1 - i0 + 1) for j in range(j0, c2 - j0 + 1))
                    flow = 0; perpoint = {}
                    for i in range(i0, c1 - i0 + 1):
                        for j in range(j0, c2 - j0 + 1):
                            for e in E:
                                a = (i, j); ae = (i + e[0], j + e[1])
                                if inB(ae): continue
                                b = (c1 - i - e[0], c2 - j - e[1])
                                t = H(k, a) * H(k - 1, b) - H(k - 1, a) * H(k, b)
                                flow += t; terms += 1; term_neg += t < 0
                                perpoint[a] = perpoint.get(a, 0) + t
                    boxes += 1; ident_bad += flow != direct
                    point_neg += sum(1 for v in perpoint.values() if v < 0)
print(f'{boxes} boxes: identity mismatches {ident_bad}; {terms} flow terms, {term_neg} negative; boundary points with negative grouped value: {point_neg}')
