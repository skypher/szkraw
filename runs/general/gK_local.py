"""Degree-K versions of the G_1 local inequalities (kappa = 1/2), with the closed-form weights
W_{i,j}(r,a) = sum_{i'>=i, j'>=0} C(i'-i+j, j) C(a,i') C(r,j') sigma_{i'+j'}  (sigma_1 = 1, sigma_k = 0 for k > K):
 (I3)  r>=1: (1/4)[W10(r,a+1) W20(r-1,a+3) + W20(r,a+2) W10(r-1,a+3)] >= D_r W31(r-1,a+3)
 (I4a) r>=1: (1/4) W20(r,a+2) W20(r-1,a+4) >= D_r W41(r-1,a+4)
 (I4b) r>=2: (1/4)[W20(r,a+2) W21(r-2,a+4)/D_r + W21(r-1,a+2) W20(r-2,a+4)/D_{r-1}] >= W42(r-2,a+4)
Also the G_3 jumps (K >= 7) are reported separately: weights W_{7,3}, W_{8,3}, W_{8,4} (here only their size).
Grid test of min LHS/RHS on random LC and non-LC sigma of degree K."""
import sys, random
from math import comb
K = int(sys.argv[1]) if len(sys.argv) > 1 else 5
def mkW(sig):
    def W(i, j, r, a):
        if r < 0 or a < 0: return 0.0
        return sum(comb(ip - i + j, j)*comb(a, ip)*comb(r, jp)*sig[ip + jp] for ip in range(i, K+1) for jp in range(0, K+1-ip) if ip + jp >= 1)
    return W
def D(sig, n): return sum(comb(n, k)*sig[k] for k in range(1, K+1))
def ratios(sig, r, a):
    W = mkW(sig); Dr = D(sig, r); out = {}
    q = lambda x, y: x/y if y > 0 else float('inf')
    out['I3'] = q(0.25*(W(1, 0, r, a+1)*W(2, 0, r-1, a+3) + W(2, 0, r, a+2)*W(1, 0, r-1, a+3)), Dr*W(3, 1, r-1, a+3))
    out['I4a'] = q(0.25*W(2, 0, r, a+2)*W(2, 0, r-1, a+4), Dr*W(4, 1, r-1, a+4))
    if r >= 2:
        out['I4b'] = q(0.25*(W(2, 0, r, a+2)*W(2, 1, r-2, a+4)/Dr + W(2, 1, r-1, a+2)*W(2, 0, r-2, a+4)/D(sig, r-1)), W(4, 2, r-2, a+4))
    return out
rng = random.Random(3)
vals = [0, 0.001, 0.01, 0.1, 0.5, 1, 3, 10]
def lc():
    x = [rng.choice(vals) for _ in range(K-1)]
    rho = [sum(x[i:]) for i in range(K-1)]
    s = [0.0, 1.0]
    for k in range(K-1): s.append(s[-1]*rho[k])
    return s
def nonlc():
    return [0.0, 1.0] + [rng.choice(vals) for _ in range(K-1)]
for name, samp in (('LC', lc), ('nonLC', nonlc)):
    worst = {}
    for _ in range(1500):
        s = samp()
        if s[K] == 0: continue
        for r in (1, 2, 3, 4, 6, 10, 30, 100):
            for a in (0, 1, 2, 3, 5, 8, 20, 60):
                for key, v in ratios(s, r, a).items():
                    if key not in worst or v < worst[key][0]: worst[key] = (v, r, a, [round(x, 4) for x in s[2:]])
    print(f'K={K} {name:5s}: ' + '; '.join(f'{k} min {v[0]:.3f} (r={v[1]},a={v[2]},s={v[3]})' for k, v in sorted(worst.items())), flush=True)
