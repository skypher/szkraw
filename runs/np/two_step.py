"""Two-step symmetric identity for (**'): D(B) = sum_{(e,e')} [V_{e+e'}(B - e) - V_{e+e'}(B)], V_s(a) = H_{k-1}(a) H_{k-1}(c - s - a),
where D(B) = sum_{p in B} [H_k(p)H_k(c-p) - H_{k-1}(p)H_{k+1}(c-p)] (both sides with the multiplicity of ordered step pairs).
Checks the identity (up to the global factor) and the sign of each ordered and unordered (e,e') term. Usage: two_step.py Kmax"""
import sys
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def H(k, p): return C(k, p[0]) * C(p[0], k - p[1]) if k >= 0 and p[0] >= 0 and p[1] >= 0 else 0
E = [(1, 0), (0, 1), (1, 1)]
Kmax = int(sys.argv[1]); mism = 0; boxes = 0; neg = {}; negU = {}
for k in range(int(sys.argv[2]) if len(sys.argv) > 2 else 2, Kmax + 1):
    for c1 in range(0, 2 * k + 2):
        for c2 in range(0, 2 * k + 2):
            for i0 in range(0, c1 // 2 + 1):
                for j0 in range(0, c2 // 2 + 1):
                    box = [(i, j) for i in range(i0, c1 - i0 + 1) for j in range(j0, c2 - j0 + 1)]
                    direct = sum(H(k, p) * H(k, (c1 - p[0], c2 - p[1])) - H(k - 1, p) * H(k + 1, (c1 - p[0], c2 - p[1])) for p in box)
                    terms = {}
                    for e in E:
                        for f in E:
                            s = (e[0] + f[0], e[1] + f[1])
                            V = lambda a: H(k - 1, a) * H(k - 1, (c1 - s[0] - a[0], c2 - s[1] - a[1]))
                            terms[(e, f)] = sum(V((p[0] - e[0], p[1] - e[1])) for p in box) - sum(V(p) for p in box)
                    tot = sum(terms.values())
                    boxes += 1
                    if 2 * direct != tot and direct != tot: mism += 1
                    for key, v in terms.items():
                        if v < 0: neg[key] = neg.get(key, 0) + 1
                    for e in E:
                        for f in E:
                            if E.index(e) <= E.index(f):
                                u = terms[(e, f)] + (terms[(f, e)] if e != f else 0)
                                if u < 0: negU[(e, f)] = negU.get((e, f), 0) + 1
                    if boxes == 1: ratio = None
print(f'{boxes} boxes; identity mismatches (allowing factor 1 or 2): {mism}')
print('negative ordered terms:', neg)
print('negative unordered pairs:', negU)
