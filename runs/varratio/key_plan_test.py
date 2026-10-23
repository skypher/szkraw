"""Test the proof plan: Phi = P0 * L0(P1..Pa) + Q2(P1..Pa). With lam_k = coefficient of P0 P_k in Phi (k >= 1):
keep lam_1 P0 P1 (need lam_1 >= 0), keep positive lam_k P0 P_k, and replace negative lam_k P0 P_k by lam_k P1 P_{k-1}
(valid since P0 P_k <= P1 P_{k-1}). Check the Abel criterion (central sums >= 0) for the resulting quadratic form in
(P1..Pa). Exact. Usage: key_plan_test.py amax trials seed [--adv]"""
import sys, random, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
from key_cert_lp import lc_u
amax, T, rng = int(sys.argv[1]), int(sys.argv[2]), random.Random(int(sys.argv[3]))
cases = [(rng.randint(3, amax), None) for _ in range(T)]
if '--adv' in sys.argv: cases = [(a, w) for a in range(3, amax + 1) for w in [sp.Rational(1, 10), sp.Rational(1, 1000), sp.Rational(1, 10 ** 6)]]
bad_l1 = 0; bad_abel = 0
for a, w in cases:
    u = lc_u(rng, a + 3) if w is None else [1 / w, sp.Integer(1)] + [w ** (n - 1) for n in range(2, a + 4)]
    P, Lin, Quad, f1, Dc = parts(u, a)
    poly = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
    q = {}
    for m, v in zip(poly.monoms(), poly.coeffs()):
        idx = [i for i, e in enumerate(m) for _ in range(e)]
        q[(idx[0], idx[1])] = v
    lam = {k: q.get((0, k), 0) for k in range(1, a + 1)}
    if lam[1] < 0: bad_l1 += 1
    qq = {key: v for key, v in q.items() if key[0] >= 1}
    for k in range(2, a + 1):
        if lam[k] < 0:
            key = (1, k - 1); qq[key] = qq.get(key, 0) + lam[k]
    worst = None
    for s in range(2, 2 * a + 1):
        tot = 0
        for i in range(s // 2, 0, -1):
            if s - i > a: continue
            tot += qq.get((i, s - i), 0)
            if worst is None or tot < worst[0]: worst = (tot, s, i)
    if worst and worst[0] < 0:
        bad_abel += 1
        print(f'  a={a} {"rand" if w is None else "geo w=" + str(w)}: negative central sum {float(worst[0]):.4g} at (sigma,i)={worst[1:]}', flush=True)
print(f'{len(cases)} cases: lambda_1 < 0 in {bad_l1}; Abel criterion fails in {bad_abel}')
