"""tower_w search with the gauge fixed: singleton weights w_i = 1 (rescaling z_i -> s_i z_i is a symmetry of the system,
and without fixing it the solver shrinks the scale and the absolute residual to zero without converging)."""
import sys, time, numpy as np, sympy as sp
from scipy.optimize import least_squares
from tower_w import equations, profile
def solve_fixed(sig, starts, seed):
    eqs, unk = equations(3, profile(3, sig))
    fix = {x: 1 for x in unk if x.name in ('w_1', 'w_2', 'w_3')}
    eqs = [sp.expand(e.subs(fix)) for e in eqs]; unk = [x for x in unk if x not in fix]
    f = sp.lambdify(unk, eqs, 'numpy'); J = sp.lambdify(unk, sp.Matrix(eqs).jacobian(unk), 'numpy')
    rng = np.random.default_rng(seed); best = None
    for _ in range(starts):
        r = least_squares(lambda x: np.array(f(*x), dtype=float), rng.exponential(1.0, len(unk)),
                          jac=lambda x: np.array(J(*x), dtype=float), bounds=(0, np.inf), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        if best is None or r.cost < best[0]: best = (r.cost, r.x)
        if best[0] < 1e-26: break
    return best, unk
name, s, starts = sys.argv[1], sys.argv[2], int(sys.argv[3])
t0 = time.time(); (cost, x), unk = solve_fixed([sp.Rational(v) for v in s.split(',')], starts, 1)
print(f'{name:22s}: best residual {2*cost:.2e}, max parameter {x.max():.2e} ({starts} starts, {time.time()-t0:.0f}s)', flush=True)
