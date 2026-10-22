"""G_1 local inequalities in the geometric (all-degree) limit: sigma_k = rho^(k-1) for k <= K with K = 40 (effectively
infinite for r + a <= 40). Minimum ratio over r, a, rho."""
import sys
from math import comb
K = 60
def run(rho):
    sig = [0.0] + [rho**(k-1) for k in range(1, K+1)]
    def W(i, j, r, a):
        if r < 0 or a < 0: return 0.0
        return sum(comb(ip - i + j, j)*comb(a, ip)*comb(r, jp)*sig[ip + jp] for ip in range(i, min(a, K)+1) for jp in range(0, min(r, K-ip)+1) if ip + jp >= 1)
    D = lambda n: sum(comb(n, k)*sig[k] for k in range(1, min(n, K)+1))
    worst = {}
    for r in range(1, 40):
        for a in range(0, 40 - r):
            Dr = D(r)
            vals = {'I3': 0.25*(W(1, 0, r, a+1)*W(2, 0, r-1, a+3) + W(2, 0, r, a+2)*W(1, 0, r-1, a+3))/(Dr*W(3, 1, r-1, a+3)),
                    'I4a': 0.25*W(2, 0, r, a+2)*W(2, 0, r-1, a+4)/(Dr*W(4, 1, r-1, a+4))}
            if r >= 2:
                vals['I4b'] = 0.25*(W(2, 0, r, a+2)*W(2, 1, r-2, a+4)/Dr + W(2, 1, r-1, a+2)*W(2, 0, r-2, a+4)/D(r-1))/W(4, 2, r-2, a+4)
            for k, v in vals.items():
                if k not in worst or v < worst[k][0]: worst[k] = (v, r, a)
    return worst
for rho in (1e-4, 1e-3, 1e-2, 0.05, 0.1, 0.3, 1.0, 3.0):
    w = run(rho)
    print(f'geometric rho={rho}: ' + '; '.join(f'{k} min {v[0]:.3f} (r={v[1]},a={v[2]})' for k, v in sorted(w.items())), flush=True)
