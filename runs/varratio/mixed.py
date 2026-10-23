"""Mixed inequalities of the varying-ratio kernel (h-form):
f_n(l) = sum_h C(l,h) sigma_{n+h} (sigma_0 = 0), g_n(l) = sum_h C(l,h) beta_{n+h}.
MI1: g_1(l) f_n(l+1) >= d_{l+1} g_{n+1}(l)   (n >= 2)
MI2: f_2(l) g_n(l+1) >= d_{l+1} g_{n+2}(l)   (n >= 1)
for l >= 0 with all indices within the profile length.
Reports, per member class, how often MI holds and whether MI-holding members ever fail (P)."""
import sys, math, random
from fractions import Fraction as F
_HERE = __import__('os').path.dirname(__import__('os').path.abspath(__file__))
sys.path.insert(0, __import__('os').path.join(_HERE, '..', '..')); sys.path.insert(0, _HERE)
from probe import linearization, first_negative
import hform_w, hform_ctrl, hform

def newton_coeffs(seq):
    out = []; cur = list(seq)
    while cur:
        out.append(cur[0]); cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    return out

def mixed_ok(b, d):
    N = len(d) - 1
    sig = newton_coeffs(d) + [F(0)] * (N + 3)
    beta = newton_coeffs(b) + [F(0)] * (N + 3)
    f = lambda n, l: sum(math.comb(l, h) * sig[n + h] for h in range(l + 1))
    g = lambda n, l: sum(math.comb(l, h) * beta[n + h] for h in range(l + 1))
    for l in range(0, N):
        for n in range(1, N + 1):
            if n >= 2 and g(1, l) * f(n, l + 1) < d[l + 1] * g(n + 1, l): return False
            if f(2, l) * g(n, l + 1) < d[l + 1] * g(n + 2, l): return False
    return True

if __name__ == '__main__':
    import threading, time
    PROG = {'done': 0, 'cls': '', 'N': 0, 't0': time.time()}
    def _hb():
        while True:
            time.sleep(60)
            print(f"[{time.strftime('%H:%M:%S')}] heartbeat: {PROG['done']} members done, class {PROG['cls']} N={PROG['N']}, elapsed {time.time()-PROG['t0']:.0f}s", flush=True)
    threading.Thread(target=_hb, daemon=True).start()
    Ns = [int(x) for x in sys.argv[1].split(',')]; per = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    gens = {'M': lambda N: hform.member(rng, N, 'M'), 'spike': lambda N: hform_w.member(rng, N, 'spike'),
            'geo': lambda N: hform_w.member(rng, N, 'geo'), 'newton': lambda N: hform_ctrl.member(rng, N, 'newton'),
            'incr': lambda N: hform_ctrl.member(rng, N, 'incr')}
    for name, gen in gens.items():
        stats = {'MI': 0, 'noMI': 0, 'MI_fail': 0, 'noMI_fail': 0}
        for N in Ns:
            for _ in range(per):
                PROG['cls'] = name; PROG['N'] = N; PROG['done'] += 1
                a, b, c = gen(N)
                ok = mixed_ok(b, c)
                bad = first_negative(linearization(a, b, c)) is not None
                stats['MI' if ok else 'noMI'] += 1
                if bad: stats['MI_fail' if ok else 'noMI_fail'] += 1
        print(name, Ns, stats, flush=True)
