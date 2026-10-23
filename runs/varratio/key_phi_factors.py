"""Which central sums of Phi carry the factor d_{l+a} = sum_m C(a,m) u_m (or its square)? Prints, per a, the sigma range
with the factor and the cofactor of the top sum. Usage: key_phi_factors.py amax"""
import sys, math
import sympy as sp
sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from key_phi import parts
amax = int(sys.argv[1])
for a in range(3, amax + 1):
    U = sp.symbols('u0:%d' % (a + 1))
    P, Lin, Quad, f1, Dc = parts(list(U) + [sp.Integer(0)] * 3, a)
    poly = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
    q = {}
    for m, v in zip(poly.monoms(), poly.coeffs()):
        idx = [i for i, e in enumerate(m) for _ in range(e)]
        q[(idx[0], idx[1])] = sp.expand(v)
    dla = sum(math.comb(a, m) * U[m] for m in range(a + 1))
    rows = []
    for s in range(1, 2 * a + 1):
        tot = 0; flags = []
        for i in range(s // 2, -1, -1):
            if s - i > a: continue
            tot = sp.expand(tot + q.get((i, s - i), 0))
            if tot == 0: continue
            r1 = sp.rem(sp.Poly(tot, *U), sp.Poly(dla, *U)).is_zero
            r2 = r1 and sp.rem(sp.Poly(sp.cancel(tot / dla), *U), sp.Poly(dla, *U)).is_zero
            flags.append('d^2' if r2 else ('d' if r1 else '-'))
        rows.append((s, ''.join(f[0] if f != 'd^2' else '2' for f in flags)))
    top = sp.factor(sp.cancel(q.get((a, a), 0) / dla ** 2))
    print(f'a={a}: factor pattern per sigma (d = d_l+a divides, 2 = d^2, - = no):', ' '.join(f'{s}:{fl}' for s, fl in rows))
    print(f'   top cofactor P_a^2: {top}', flush=True)
