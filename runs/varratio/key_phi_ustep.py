"""Second (profile) step of the key certificate: every central sum S(u) of Phi (cubic in u) is certified >= 0 for all
LC u by an EXACT LP certificate with generators u_k (u_{i+1} u_{j-1} - u_i u_j) (i+1 <= j-1; Robin Hood transfers)
and monomials u_i u_j u_k. Uses key_cert_exact.certify (float LP for support, exact rational re-solve and check).
Usage: key_phi_ustep.py amax"""
import sys, itertools, threading, time
from fractions import Fraction as Fr
import sympy as sp
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, _HERE)
from key_phi import parts
from key_cert_exact import certify

def certificate_for(S, U):
    nU = len(U)
    gens = []
    for k in range(nU):
        for i in range(nU):
            for j in range(i + 2, nU):
                gens.append(sp.expand(U[k] * (U[i + 1] * U[j - 1] - U[i] * U[j])))
    for c in itertools.combinations_with_replacement(range(nU), 3):
        gens.append(U[c[0]] * U[c[1]] * U[c[2]])
    polys = [sp.Poly(g, *U) for g in gens]; Ps = sp.Poly(S, *U)
    monos = sorted(set(m for p in polys + [Ps] for m in p.monoms())); idx = {m: t for t, m in enumerate(monos)}
    A = [[Fr(0)] * len(polys) for _ in monos]
    for col, p in enumerate(polys):
        for m, v in zip(p.monoms(), p.coeffs()): A[idx[m]][col] = Fr(int(v))
    bv = [Fr(0)] * len(monos)
    for m, v in zip(Ps.monoms(), Ps.coeffs()): bv[idx[m]] = Fr(int(sp.numer(v)), int(sp.denom(v)))
    return certify(A, bv)[0]

if __name__ == '__main__':
    amax = int(sys.argv[1]); amin = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    CUR = {'item': 'start', 'done': 0}; t0 = time.time()
    def _hb():
        while True:
            time.sleep(60)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {CUR['done']} sums certified so far, at {CUR['item']}, elapsed {time.time()-t0:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    for a in range(amin, amax + 1):
        U = sp.symbols('u0:%d' % (a + 1))
        P, Lin, Quad, f1, Dc = parts(list(U) + [sp.Integer(0)] * 3, a)
        poly = sp.Poly(sp.expand(Lin * Dc - f1 * Quad), *P)
        q = {}
        for m, v in zip(poly.monoms(), poly.coeffs()):
            idx = [i for i, e in enumerate(m) for _ in range(e)]
            q[(idx[0], idx[1])] = sp.expand(v)
        verdicts = {}
        for s in range(1, 2 * a + 1):
            tot = 0
            for i in range(s // 2, -1, -1):
                if s - i > a: continue
                tot = sp.expand(tot + q.get((i, s - i), 0))
                if tot == 0: continue
                CUR['item'] = f'a={a} sigma={s} i={i}'
                v = certificate_for(tot, U); CUR['done'] += 1
                verdicts[v] = verdicts.get(v, 0) + 1
                if v != 'CERTIFIED': print(f'  a={a} sigma={s} i={i}: {v}', flush=True)
        print(f'a={a}: central sums {verdicts}', flush=True)
        assert set(verdicts) <= {'CERTIFIED'}, f'a={a}: uncertified central sum'
