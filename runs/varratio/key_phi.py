"""Top-constraint reduction of the full key. For fixed u (LC), Key(P) = Lin(P) - Quad(P) (Lin linear, Quad quadratic in
P = (P_0..P_a), P_k = D^k rho(l)); with g_top(P) = f_1(l+a-1) - Dc(l+a-1)(P) >= 0, Key >= 0 on the feasible ray segment iff
Phi(P) = Lin(P) Dc(l+a-1)(P) - f_1(l+a-1) Quad(P) >= 0. Test the Abel criterion for Phi on LC P: every central partial sum of
every anti-diagonal of Phi's symmetric coefficient matrix is >= 0 (exact). Usage: key_phi.py amax trials seed [--adv]"""
import sys, random, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_cert_lp import lc_u

def parts(u, a):
    P = sp.symbols('P0:%d' % (a + 1))
    rho = lambda n: sum(math.comb(n, k) * P[k] for k in range(min(n, a) + 1))
    d = lambda n: sum(math.comb(n, m) * u[m] for m in range(n + 1))
    c = lambda n: rho(n) * d(n)
    X = d(a) - d(0); Xp = d(a - 1) - d(1)
    B0 = c(a) - c(0) - a * (c(1) - c(0)); B0p = c(a) - c(1) - (a - 1) * (c(2) - c(1))
    Hs = sum((n - 2) * math.comb(a, n) * u[n] for n in range(3, a + 1))
    Z1 = sum((n - 2) * math.comb(a, n) * rho(n) * u[n] for n in range(3, a + 1))
    V1 = sum((n - 2) * math.comb(a, n) * n * (rho(n) - rho(n - 1)) * u[n - 1] for n in range(3, a + 1))
    CX = c(a) - c(0); CXp = c(a - 1) - c(1)
    Lin = sp.expand(X * B0p + B0 * Xp - 4 * c(1) * Hs)
    Quad = sp.expand(CX * B0p + B0 * CXp - 4 * c(1) * Z1 - 2 * c(1) * V1)
    f1top = d(a) - d(a - 1); Dctop = sp.expand(c(a) - c(a - 1))
    return P, Lin, Quad, f1top, Dctop

def abel_min(Phi, P, a):
    poly = sp.Poly(Phi, *P)
    q = {}
    for m, v in zip(poly.monoms(), poly.coeffs()):
        idx = [i for i, e in enumerate(m) for _ in range(e)]
        q[(idx[0], idx[1])] = v  # i <= j, coefficient of P_i P_j
    worst = None
    for s in range(0, 2 * a + 1):
        tot = 0
        for i in range(s // 2, -1, -1):
            j = s - i
            if j > a: continue
            tot += q.get((i, j), 0)
            if (s, i) != (0, 0) and (worst is None or tot < worst[0]): worst = (tot, s, i)
    return worst

if __name__ == '__main__':
    amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
    cases = [(rng.randint(3, amax), None) for _ in range(T)]
    if '--adv' in sys.argv:
        alist = [int(z) for z in sys.argv[sys.argv.index('--adv') + 1].split(',')] if len(sys.argv) > sys.argv.index('--adv') + 1 else range(3, amax + 1)
        cases = [(a, w) for a in alist for w in [sp.Rational(1, 10), sp.Rational(1, 100), sp.Rational(1, 1000), sp.Rational(1, 10 ** 6)]]
    neg = 0
    for a, w in cases:
        u = lc_u(rng, a + 3) if w is None else [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]
        P, Lin, Quad, f1top, Dctop = parts(u, a)
        Phi = sp.expand(Lin * Dctop - f1top * Quad)
        wm = abel_min(Phi, P, a)
        bad = bool(wm[0] < 0)
        neg += bad
        print(f'a={a} {"rand" if w is None else "geo w=" + str(w)}: min central sum {float(wm[0]):.4g} at (sigma, i)={wm[1:]} {"NEGATIVE" if bad else ""}', flush=True)
    print('cases with a negative central sum:', neg)
