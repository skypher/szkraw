"""Explicit closed forms of the central sums S_{sigma,1} and S_{sigma,0} of Phi, checked symbolically for a = 3..amax.
M_{km} = B0'^(k) E1^(m) + B0^(k) E2^(m) + c1^(k) E3^(m); S_{sigma,i} = sum_{k=i}^{sigma-i} M_{k,sigma-k}.
Usage: key_S_low.py amax"""
import sys, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
C = math.comb

def pieces(u, a):
    d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
    A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2); Fv = A - B
    y = lambda n: C(a, n) * u[n]
    Y = sum(y(n) for n in range(2, a + 1)); Yp = sum(C(a - 1, n) * (u[n] + u[n + 1]) for n in range(2, a))
    def B0(k):
        if k == 0: return Y
        if k == 1: return a * (A - d1)
        return C(a, k) * A
    def B0p(k):
        if k == 0: return Yp
        if k == 1: return a * A - 2 * (a - 1) * d2 + (a - 2) * d1
        if k == 2: return C(a, 2) * A - (a - 1) * d2
        return C(a, k) * A
    def E1(m):
        if m == 0: return 0
        return C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
    def E2(m):
        if m == 0: return 0
        v = C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1)
        return v + d1 * Fv if m == 1 else v
    def V1(m): return sum((n - 2) * C(a, n) * n * C(n - 1, m - 1) * u[n - 1] for n in range(3, a + 1))
    def E3(m):
        if m == 0: return 0
        return 2 * Fv * V1(m) - 4 * sum((n - 2) * y(n) * (Fv * (C(a, m) - C(n, m)) + C(a - 1, m - 1) * B) for n in range(3, a + 1))
    c1 = lambda k: d1 if k <= 1 else 0
    M = lambda k, m: B0p(k) * E1(m) + B0(k) * E2(m) + c1(k) * E3(m)
    return M

if __name__ == '__main__':
    amax = int(sys.argv[1])
    for a in range(3, amax + 1):
        U = sp.symbols('u0:%d' % (a + 1)); u = list(U) + [sp.Integer(0)] * 3
        P, Lin, Quad, f1, Dc = parts(u, a)
        poly = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
        q = {}
        for mm, v in zip(poly.monoms(), poly.coeffs()):
            idx = [i for i, e in enumerate(mm) for _ in range(e)]
            q[(idx[0], idx[1])] = sp.expand(v)
        M = pieces(u, a); ok = True; cnt = 0
        for s in range(1, 2 * a + 1):
            for i in (0, 1):
                if i > s // 2: continue
                ks = [k for k in range(i, s - i + 1) if k <= a and s - k <= a]
                if not ks: continue
                direct = sp.expand(sum(q.get((k, s - k), 0) for k in range(i, s // 2 + 1) if s - k <= a))
                closed = sp.expand(sum(M(k, s - k) for k in ks))
                cnt += 1
                if direct != closed: ok = False; print(f'  mismatch a={a} sigma={s} i={i}')
        print(f'a={a}: {cnt} central sums with i in {{0,1}}: closed forms {"MATCH" if ok else "DIFFER"}', flush=True)
