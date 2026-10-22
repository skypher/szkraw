"""(**') for (NP): H_k(i,j) = [y^i w^j](y + w + yw)^k = C(k,i) C(i,k-j). For every centre c = (c1,c2) and box
[i0, c1-i0] x [j0, c2-j0], Box = sum_{(i,j) in box} [H_k(i,j) H_k(c-(i,j)) - H_{k-1}(i,j) H_{k+1}(c-(i,j))] >= 0?
(2D Abel summation in rho and nu then gives kappa_k^2 >= kappa_{k-1} kappa_{k+1} for all LC rho, nu.) Usage: trinomial_boxes.py Kmax"""
import sys
from math import comb
def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0
def H(k, i, j): return C(k, i) * C(i, k - j) if k >= 0 else 0
Kmax = int(sys.argv[1]); cnt = 0; neg = 0; worst = None
for k in range(1, Kmax + 1):
    for c1 in range(0, 2 * k + 2):
        for c2 in range(0, 2 * k + 2):
            T = {}
            for i in range(0, c1 + 1):
                for j in range(0, c2 + 1):
                    T[(i, j)] = H(k, i, j) * H(k, c1 - i, c2 - j) - H(k - 1, i, j) * H(k + 1, c1 - i, c2 - j)
            for i0 in range(0, c1 // 2 + 1):
                for j0 in range(0, c2 // 2 + 1):
                    s = sum(T[(i, j)] for i in range(i0, c1 - i0 + 1) for j in range(j0, c2 - j0 + 1))
                    cnt += 1
                    if s < 0:
                        neg += 1
                        if worst is None or s < worst[0]: worst = (s, k, c1, c2, i0, j0)
print(f'{cnt} boxes, {neg} negative; worst {worst}')
