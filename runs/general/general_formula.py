"""Check the conjectured general kernel recurrence for degree K (node (r+1, a)):
D_{r+1} c_{r+1,a} = T c_{r,a} + sum_{j>=0} sum_{e in 0,1,2} s(e,j) t^[e=1] W_{2j+e,j}(r-j, a+2j+e) c_{r-j, a+2j+e},
W_{i,j}(r,a) = sum_{i'>=i, j'>=0} C(i'-i+j, j) C(a,i') C(r,j') sigma_{i'+j'},  s(1,j) = s(2,j) = (-1)^j, s(0,j) = (-1)^(j+1),
against the symbolic-exponent coefficients of cubic_symbolic.G(K)."""
import sys, sympy as sp
from cubic_symbolic import G
a_, r_, t_, T_ = sp.symbols('a r t T')
K = int(sys.argv[1])
sig = [sp.Integer(1)] + list(sp.symbols(f's2:{K+1}'))
g = G(K, sig)
Cb = lambda n, k: sp.expand_func(sp.binomial(n, k))
def W(i, j, r, a):
    return sum(sp.binomial(ip - i + j, j)*Cb(a, ip)*Cb(r, jp)*sig[ip + jp - 1] for ip in range(i, K+1) for jp in range(0, K+1 - ip) if ip + jp >= 1)
pred = {}
for j in range(0, K):
    for e in (0, 1, 2):
        i = 2*j + e
        if i > K: continue
        s = (-1)**(j + 1) if e == 0 else (-1)**j
        pred[(-i, j)] = sp.expand(s*(t_ if e == 1 else 1)*W(i, j, r_, a_))
pred[(0, 0)] = sp.expand(T_ + pred.get((0, 0), 0))
pred[(0, -1)] = -sp.expand(sum(Cb(r_, k)*sig[k-1] for k in range(1, K+1)))
bad = [k for k in set(g) | set(pred) if sp.expand(sp.expand_func(g.get(k, 0)) - pred.get(k, 0)) != 0]
print(f'K={K}: {len(g)} shifts from the operator, {len(pred)} predicted, mismatches: {bad}', flush=True)
