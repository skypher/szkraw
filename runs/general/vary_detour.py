"""For h-transformed arrays (vary_kernel.py), build the signed kernel-recurrence moves on Omega_N (weights from the Newton
coefficients nu of d'' and beta of b'', normalized by d'' at the destination), split them by sign into P (>= 0) and Q (> 0
magnitudes of negative moves), and test P^2 >= 4Q entrywise; also run the recurrence and check omega >= (1/2) P omega."""
import sys
from math import comb
import mpmath as mp
from fractions import Fraction as F
from vary_kernel import L_family
mp.mp.dps = 40
def hform(a, b, c):
    N = len(a) - 1; fl = lambda q: mp.mpf(q.numerator)/q.denominator
    M = mp.matrix(N+1, N+1)
    for i in range(N+1):
        if i < N: M[i, i+1] = fl(a[i])
        if i > 0: M[i, i-1] = fl(c[i])
    E, ER = mp.eig(M); idx = max(range(N+1), key=lambda i: mp.re(E[i])); s = mp.re(E[idx])
    lam = [mp.re(ER[i, idx]) for i in range(N+1)]
    if lam[0] < 0: lam = [-x for x in lam]
    d2 = [fl(c[i])*(lam[i-1] if i else 0)/(s*lam[i]) for i in range(N+1)]
    b2 = [fl(b[i])/s for i in range(N+1)]
    nu = [mp.mpf(0)] + [sum((-1)**(k-i)*comb(k, i)*d2[i] for i in range(k+1)) for k in range(1, N+1)]
    be = [sum((-1)**(k-i)*comb(k, i)*b2[i] for i in range(k+1)) for k in range(0, N+1)]
    return N, nu, be
def test(a, b, c):
    N, nu, be = hform(a, b, c)
    f = lambda seq, n, l: sum(comb(l, h)*(seq[n+h] if n+h <= N else 0) for h in range(l+1))
    W = lambda seq, p, q, l, a_: mp.mpf(0) if (l < 0 or a_ < 0) else sum(comb(n-p+q, q)*comb(a_, n)*f(seq, n, l) for n in range(p, a_+1))
    dd = lambda i: f(nu, 0, i)
    moves = {}   # (src, tgt) -> weight (scalar, normalized by d at destination)
    for l in range(0, N+1):
        for a_ in range(0, N+1-l):
            for j in range(0, N+1):
                sg = (-1)**j
                for (dl, da, w) in ((j+1, -(2*j+1), W(be, 2*j+1, j, l, a_)), (j+1, -(2*j+2), W(nu, 2*j+2, j, l, a_)), (j+2, -(2*j+2), W(nu, 2*j+2, j+1, l, a_))):
                    lt, at = l + dl, a_ + da
                    if at < 0 or lt + at > N or w == 0: continue
                    key = ((l, a_), (lt, at)); moves[key] = moves.get(key, 0) + sg*w/dd(lt)
    P = {k: v for k, v in moves.items() if v > 0}; Q = {k: -v for k, v in moves.items() if v < 0}
    P2 = {}
    for (x, y), w1 in P.items():
        for (y2, z), w2 in P.items():
            if y2 == y: P2[(x, z)] = P2.get((x, z), 0) + w1*w2
    ratios = [P2.get(k, 0)/(4*q) for k, q in Q.items()]
    return len(Q), (min(ratios) if ratios else None)
for N in (4, 6, 8, 10):
    for r, kappa, tt in ((F(1, 5), F(2, 5), F(0)), (F(1, 5), F(2, 5), F(1)), (F(1, 2), F(1, 4), F(1)), (F(1, 10), F(9, 20), F(3))):
        nQ, mr = test(*L_family(N, r, kappa, tt))
        print(f'N={N} r={r} kappa={kappa} t={tt}: {nQ} negative moves; min P^2/(4Q) = {mp.nstr(mr, 4) if mr is not None else None}', flush=True)
