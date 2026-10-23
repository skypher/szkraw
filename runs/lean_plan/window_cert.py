"""Window certificates for the Lean proof of Theorem 8.16: MM1 = M_{1,m} + M_{m,1} (3 <= a <= 5, 2 <= m <= a) and
S20 = M_{0,2} + M_{1,1} (3 <= a <= 4), with MC built from the Lean definitions in lean/Szkraw/GenKey.lean.
Generators: u_k (u_{i+1} u_{j-1} - u_i u_j) (i+1 <= j-1) and monomials u_i u_j u_k. Exact LP via key_cert_exact.certify.
Writes the window theorems (one per item) to OUT when given. Usage: window_cert.py [OUT]"""
import sys, os, itertools
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'varratio'))
from key_cert_exact import certify

C = sp.binomial

def mc_builder(a):
    u = sp.symbols('u0:%d' % (a + 1))
    U = lambda n: u[n] if 0 <= n <= a else 0
    dd = lambda n: sum(C(n, k) * U(k) for k in range(n + 1))
    w = lambda n: (n - 2) if n >= 3 else 0
    H = sum(w(n) * C(a, n) * U(n) for n in range(a + 1))
    zeta = lambda k: sum(w(n) * C(a, n) * U(n) * C(n, k) for n in range(a + 1))
    nu = lambda k: sum(w(n) * C(a, n) * n * U(n - 1) * (C(n - 1, k - 1) if k >= 1 else 0) for n in range(a + 1))
    chi = lambda k: C(a, k) * dd(a) - C(0, k) * dd(0)
    chip = lambda k: C(a - 1, k) * dd(a - 1) - C(1, k) * dd(1)
    beta = lambda k: C(a, k) * dd(a) - C(0, k) * dd(0) - a * (C(1, k) * dd(1) - C(0, k) * dd(0))
    betap = lambda k: C(a, k) * dd(a) + (a - 2) * C(1, k) * dd(1) - (a - 1) * C(2, k) * dd(2)
    delta = lambda k: C(a, k) * dd(a) - C(a - 1, k) * dd(a - 1)
    X, Xp, F = dd(a) - dd(0), dd(a - 1) - dd(1), dd(a) - dd(a - 1)
    def MC(k, m):
        return sp.expand(betap(k) * (X * delta(m) - F * chi(m)) + beta(k) * (Xp * delta(m) - F * chip(m)) +
                         (1 if k <= 1 else 0) * dd(1) * (2 * F * nu(m) - 4 * (H * delta(m) - F * zeta(m))))
    return u, MC

def cert(S, U):
    nU = len(U); gens, labels = [], []
    for k in range(nU):
        for i in range(nU):
            for j in range(i + 2, nU):
                gens.append(sp.expand(U[k] * (U[i + 1] * U[j - 1] - U[i] * U[j]))); labels.append(('lc', k, i, j))
    for c in itertools.combinations_with_replacement(range(nU), 3):
        gens.append(U[c[0]] * U[c[1]] * U[c[2]]); labels.append(('mono',) + c)
    polys = [sp.Poly(g, *U) for g in gens]; Ps = sp.Poly(S, *U)
    monos = sorted(set(m for p in polys + [Ps] for m in p.monoms())); idx = {m: t for t, m in enumerate(monos)}
    A = [[Fr(0)] * len(polys) for _ in monos]
    for col, p in enumerate(polys):
        for m, v in zip(p.monoms(), p.coeffs()): A[idx[m]][col] = Fr(int(v))
    bv = [Fr(0)] * len(monos)
    for m, v in zip(Ps.monoms(), Ps.coeffs()): bv[idx[m]] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    verdict, x = certify(A, bv)
    if verdict != 'CERTIFIED': return verdict, None
    used = [(x[j], labels[j]) for j in range(len(labels)) if x[j] != 0]
    # independent exact check
    tot = sum(sp.Rational(c.numerator, c.denominator) * gens[labels.index(l)] for c, l in used)
    assert sp.expand(tot - S) == 0
    return verdict, used

def lean_hint(l):
    if l[0] == 'lc':
        _, k, i, j = l
        return f'mul_nonneg (hf.1 {k}) (sub_nonneg.2 (hf.step (x := {i}) (y := {j - 2}) (by norm_num)))'
    _, i, j, k = l
    return f'mul_nonneg (mul_nonneg (hf.1 {i}) (hf.1 {j})) (hf.1 {k})'

def lean_have(n, l):
    if l[0] == 'lc':
        _, k, i, j = l
        return (f'  have g{n} : 0 ≤ f {k} * (f {i + 1} * f {j - 1} - f {i} * f {j}) := '
                f'mul_nonneg (hf.1 {k}) (sub_nonneg.2 (hf.step (x := {i}) (y := {j - 2}) (by norm_num)))')
    _, i, j, k = l
    return f'  have g{n} : 0 ≤ f {i} * f {j} * f {k} := mul_nonneg (mul_nonneg (hf.1 {i}) (hf.1 {j})) (hf.1 {k})'

def lean_thm(name, stmt, used):
    lines = [f'theorem {name} {{f : ℕ → ℝ}} (hf : LCNZ f) : 0 ≤ {stmt} := by']
    lines += [lean_have(n, l) for n, (_, l) in enumerate(used)]
    lines += ['  win_expand', '  linarith']
    return '\n'.join(lines)

if __name__ == '__main__':
    ok = True; thms = []
    for a in (3, 4, 5):
        u, MC = mc_builder(a)
        items = [(f'MM1 a={a} m={m}', MC(1, m) + MC(m, 1), f'win_MM1_{a}_{m}', f'MC f {a} 1 {m} + MC f {a} {m} 1')
                 for m in range(2, a + 1)]
        if a <= 4: items.append((f'S20 a={a}', MC(0, 2) + MC(1, 1), f'win_S20_{a}', f'MC f {a} 0 2 + MC f {a} 1 1'))
        for name, S, lname, lstmt in items:
            v, used = cert(sp.expand(S), list(u))
            print(f'{name}: {v}', flush=True)
            if used is None: ok = False; continue
            thms.append(lean_thm(lname, lstmt, used))
    print('ALL CERTIFIED' if ok else 'SOME FAILED')
    if len(sys.argv) > 1:
        open(sys.argv[1], 'w').write('\n\n'.join(thms) + '\n')
