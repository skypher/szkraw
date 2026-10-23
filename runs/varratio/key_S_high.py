"""Closed form of the central sums S_{sigma,i} of Phi for i >= 2:
S = sum_{k=i}^{sigma-i} [B0'^(k) E1^(sigma-k) + B0^(k) E2^(sigma-k)], with (A = d_{l+a}, B = d_{l+a-1})
B0^(k) = C(a,k) A, B0'^(k) = C(a,k) A - [k=2](a-1) d_{l+2},
E1^(m) = C(a,m) A (B - d_l) - C(a-1,m) B (A - d_l), E2^(m) = C(a,m) A (B - d_{l+1}) - C(a-1,m) B (A - d_{l+1}).
Checked against the symbolic central sums of Phi, a = 3..amax. Usage: key_S_high.py amax"""
import sys, math
import sympy as sp
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_phi import parts
C = math.comb
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1)); u = list(U) + [sp.Integer(0)] * 3
    P, Lin, Quad, f1, Dc = parts(u, a)
    poly = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
    q = {}
    for m, v in zip(poly.monoms(), poly.coeffs()):
        idx = [i for i, e in enumerate(m) for _ in range(e)]
        q[(idx[0], idx[1])] = sp.expand(v)
    d = lambda n: sum(C(n, m) * u[m] for m in range(n + 1))
    A, B, d0, d1, d2 = d(a), d(a - 1), d(0), d(1), d(2)
    B0 = lambda k: C(a, k) * A
    B0p = lambda k: C(a, k) * A - (a - 1) * d2 if k == 2 else C(a, k) * A
    E1 = lambda m: C(a, m) * A * (B - d0) - C(a - 1, m) * B * (A - d0)
    E2 = lambda m: C(a, m) * A * (B - d1) - C(a - 1, m) * B * (A - d1)
    ok = True; cnt = 0
    for s in range(4, 2 * a + 1):
        for i in range(2, s // 2 + 1):
            if s - i > a: continue
            direct = sp.expand(sum(q.get((k, s - k), 0) for k in range(i, s // 2 + 1) if s - k <= a))
            closed = sp.expand(sum(B0p(k) * E1(s - k) + B0(k) * E2(s - k) for k in range(i, s - i + 1) if s - k <= a and k <= a))
            cnt += 1
            if direct != closed: ok = False
    print(f'a={a}: {cnt} central sums with i>=2: closed form {"MATCHES" if ok else "DIFFERS"}', flush=True)
