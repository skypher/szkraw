"""Corner sensitivity at K(N,r) for fixed r < 1 (Section 8); diagnostics. Needs mpmath and numpy.

Exact first-order formula (derivation in RESEARCH.md) for the terminal coordinate (delta c_N = 1, delta b_N = -1):
  d/de g(N,N;N) = N(-r)/(1+r)^(2N) * int_gamma [ (1+rw)^N (1-r^2/w)^(N-1) + r (1-w)^N (1+r^3/w)^(N-1) ] dw/w^2,
gamma from w = 1 to w = -r through the upper half-plane. Steepest descent at the saddles w = i r^(1/2) and
w = i r^(3/2) gives |derivative| ~ sqrt(N) rho(r)^N |cos(2N arctan r^(3/2) + psi)|, rho(r) = (1 - r + r^2)/(1 + r),
while g(N,N;N) = (1-r)^N; rho(r) > 1 - r exactly when r > 1/2.

Checks:
1. the contour formula against exact first-order derivatives;
2. the asymptotic form, by least squares over N = 30..60 (relative residual);
3. exact corner g(N,N;N) at eps_N = 3 (1-r)^N / |derivative| along the sign of the terminal direction that makes the
   first-order change negative: -2 (1-r)^N means the linear regime, i.e. (P) fails at exponentially small size.
"""
import argparse
import math
from fractions import Fraction as F
from rigidity_probe import lin_dual, krawr, direction

def derivative(N, r):
    a, b, c = krawr(N, r)
    return lin_dual(a, b, c, *direction(N, ('c', N)))[N][N][N][1]

def contour(N, r):
    import mpmath as mp
    mp.mp.dps = 40
    r = mp.mpf(r)
    f = lambda w: ((1 + r*w)**N*(1 - r**2/w)**(N-1) + r*(1 - w)**N*(1 + r**3/w)**(N-1))/w**2
    path = lambda t: (1+r)/2*mp.e**(1j*mp.pi*t) + (1-r)/2
    dpath = lambda t: (1+r)/2*1j*mp.pi*mp.e**(1j*mp.pi*t)
    return (N*(-r)/(1+r)**(2*N)*mp.quad(lambda t: f(path(t))*dpath(t), [0, 0.5, 1])).real

def corner(a, b, c):
    N = len(a)-1
    prev = [F(0)]*(N+1); cur = [F(int(i == N)) for i in range(N+1)]
    for m in range(N):
        nxt = []
        for i in range(N+1):
            v = (b[i]-b[m])*cur[i] - c[m]*prev[i]
            if i: v += c[i]*cur[i-1]
            if i < N: v += a[i]*cur[i+1]
            nxt.append(v/a[m])
        prev, cur = cur, nxt
    return cur[N]

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.parse_args()
    import numpy as np
    worst = 0.0
    for N in (2, 3, 4, 6, 9, 12):
        for r in (F(1, 2), F(3, 5), F(4, 5), F(19, 20), F(1)):
            ex = float(derivative(N, r)); fo = float(contour(N, float(r)))
            worst = max(worst, abs(ex - fo)/max(abs(ex), 1e-300))
    print(f'1. contour formula vs exact derivative, N in 2..12, r in {{1/2,3/5,4/5,19/20,1}}: max relative error {worst:.1e}', flush=True)
    for r in (F(3, 5), F(4, 5), F(19, 20)):
        rho = (1 - r + r*r)/(1 + r); phi = math.atan(float(r)**1.5)
        Ns = list(range(30, 61, 3))
        y = np.array([float(derivative(N, r)/rho**N)/math.sqrt(N) for N in Ns])
        M = np.array([[math.cos(2*n*phi), math.sin(2*n*phi)] for n in Ns])
        coef, *_ = np.linalg.lstsq(M, y, rcond=None)
        res = max(abs(M @ coef - y))/max(abs(y))
        print(f'2. r={r}: derivative/(sqrt(N) rho^N) = {coef[0]:+.3f} cos(2N phi) {coef[1]:+.3f} sin(2N phi) + residual {res:.3f}', flush=True)
    for r in (F(3, 5), F(4, 5), F(19, 20)):
        out = []
        for N in range(8, 41, 4):
            d = derivative(N, r); sgn = -1 if d > 0 else 1
            eps = 3*(1-r)**N/abs(d)
            a, b, c = krawr(N, r); b, c = list(b), list(c)
            c[N] += sgn*eps; b[N] -= sgn*eps
            out.append(f'{N}:{float(corner(a, b, c)/(1-r)**N):+.2f}')
        print(f'3. r={r}: g(N,N;N)/(1-r)^N at eps_N = 3(1-r)^N/|derivative|: ' + ' '.join(out), flush=True)

if __name__ == '__main__':
    main()
