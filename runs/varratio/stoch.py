"""Criterion S, in the paper's stochastic normalization (a + b + c = 1, b_0 = 0, a_N = 0):
c has Newton coefficients nu_k >= 0 log-concave without internal zeros;
b has Newton coefficients beta_k = w_k nu_k (k >= 1), beta_0 = 0, with w by mode;
scale b, c together so that b_N + c_N = 1; a = 1 - b - c.
modes: M (w nonincreasing), inc (w nondecreasing), spike, rand (w random), indep (b Newton LC independent of c: control)
Also reports the mixed inequalities (relative to c) and the ratio c_i/(b_i+c_i)."""
import sys, math, random, time, threading
from fractions import Fraction as F
sys.path.insert(0, '/home/yang/szkraw'); sys.path.insert(0, '/home/yang/szkraw/runs/varratio')
from probe import linearization, first_negative
from hform import lc_seq
from mixed import newton_coeffs, mixed_ok

def member(rng, N, mode):
    nu = lc_seq(rng, N)
    sc = rng.choice([F(1, 100), F(1, 10), F(1), F(5), F(50)])
    if mode == 'M': ws = sorted((sc * F(rng.randint(0, 1000), 1000) for _ in range(N)), reverse=True)
    elif mode == 'inc': ws = sorted(sc * F(rng.randint(0, 1000), 1000) for _ in range(N))
    elif mode == 'rand': ws = [sc * F(rng.randint(0, 1000), 1000) for _ in range(N)]
    elif mode == 'spike':
        ws = [sc * F(rng.randint(0, 100), 1000) for _ in range(N)]; ws[rng.randrange(N)] = sc * 50
    if mode == 'indep': beta = [F(0)] + [x * sc for x in lc_seq(rng, N)]
    else: beta = [F(0)] + [w * x for w, x in zip(ws, nu)]
    C = [sum(math.comb(n, k) * nu[k - 1] for k in range(1, n + 1)) for n in range(N + 1)]
    B = [sum(math.comb(n, k) * beta[k] for k in range(1, n + 1)) for n in range(N + 1)]
    lam = 1 / (B[N] + C[N])
    b = [x * lam for x in B]; c = [x * lam for x in C]
    a = [1 - x - y for x, y in zip(b, c)]
    return a, b, c

if __name__ == '__main__':
    PROG = {'done': 0, 'msg': '', 't0': time.time()}
    def _hb():
        while True:
            time.sleep(60)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {PROG['done']} done, {PROG['msg']}, elapsed {time.time()-PROG['t0']:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    modes = sys.argv[4].split(',')
    for mode in modes:
        st = {'MI': 0, 'noMI': 0, 'MI_fail': 0, 'noMI_fail': 0, 'ratio_nondecr': 0, 'ratio_const': 0}
        ex = None
        for N in Ns:
            for _ in range(per):
                PROG['done'] += 1; PROG['msg'] = f'{mode} N={N}'
                a, b, c = member(rng, N, mode)
                ok = mixed_ok(b, c)
                bad = first_negative(linearization(a, b, c)) is not None
                st['MI' if ok else 'noMI'] += 1
                if bad:
                    st['MI_fail' if ok else 'noMI_fail'] += 1
                    if ok and ex is None: ex = (N, [str(x) for x in b], [str(x) for x in c])
                rho = [c[i] / (b[i] + c[i]) for i in range(1, N + 1)]
                if all(rho[i + 1] >= rho[i] for i in range(N - 1)): st['ratio_nondecr'] += 1
                if len(set(rho)) == 1: st['ratio_const'] += 1
        print(mode, Ns, st, ('example MI-failure: ' + str(ex)) if ex else '', flush=True)
