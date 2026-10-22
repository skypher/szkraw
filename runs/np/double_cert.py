"""Double anti-diagonal certificate for (NP). S(alpha,beta) = sum_{n,n'} nu_n nu_n' W[n][n'] with
W[n][n'] = sum_{a=alpha}^{beta} [C(k,n)C(k,n')C(n-1,k-a)C(n'-1,k-b) - C(k-1,n)C(k+1,n')C(n-1,k-1-a)C(n'-1,k+1-b)],
b = alpha + beta - a. If on every anti-diagonal n + n' = tau of the symmetrized W all central partial sums are >= 0,
then S >= 0 for every LC nu (nu_0 = 0). Exact check over k <= Kmax, all windows. Usage: double_cert.py Kmax"""
import sys
from math import comb

def C(n, r): return comb(n, r) if 0 <= r <= n and n >= 0 else 0

def W(k, al, be):
    nmax = k + 1; w = {}
    for n in range(1, nmax + 1):
        for m in range(1, nmax + 1):
            tot = 0
            for a in range(al, be + 1):
                b = al + be - a
                tot += C(k, n) * C(k, m) * C(n - 1, k - a) * C(m - 1, k - b) - C(k - 1, n) * C(k + 1, m) * C(n - 1, k - 1 - a) * C(m - 1, k + 1 - b)
            if tot: w[(n, m)] = tot
    return w

def central_min(w):
    sym = {}
    for (n, m), v in w.items():
        a, b = min(n, m), max(n, m); sym[(a, b)] = sym.get((a, b), 0) + v
    worst = None
    for tau in set(a + b for a, b in sym):
        pairs = sorted(((a, b) for (a, b) in sym if a + b == tau), key=lambda p: -p[0])
        # include all pairs on the anti-diagonal from the centre outwards (missing pairs count as 0)
        amax = tau // 2; tot = 0
        for a in range(amax, 0, -1):
            tot += sym.get((a, tau - a), 0)
            if worst is None or tot < worst[0]: worst = (tot, tau, a)
    return worst

if __name__ == '__main__':
    Kmax = int(sys.argv[1]); glob = None; neg = 0; cnt = 0
    for k in range(2, Kmax + 1):
        for al in range(0, k + 2):
            for be in range(al, k + 2):
                w = W(k, al, be); cnt += 1
                if not w: continue
                cm = central_min(w)
                if cm[0] < 0:
                    neg += 1
                    if neg <= 5: print(f'negative central sum {cm[0]} at k={k} window=[{al},{be}] tau={cm[1]} from a={cm[2]}')
                if glob is None or cm[0] < glob[0]: glob = cm + (k, al, be)
    print(f'{cnt} (k, window) cases, {neg} with a negative central sum; minimum {glob}')
