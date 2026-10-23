"""Which convolution terms suffice for e_m >= 0 (u1-linearization)? For each form and a in [a0, amax], keep only the
product terms x_i y_j with i (or j) in a small edge set S, and test e_m >= 0 for all m. Reports failures per form.
Usage: select_test.py amax"""
import sys
sys.argv = [sys.argv[0], '3'] + sys.argv[1:]
exec(open('u1lin_test.py').read().split('fails = {}; signs = set()')[0])
amax = int(sys.argv[2])
A0 = {'L': 3, 'R': 3, 'R2': 6, "K''": 3, 'Ka': 5, 'Psi': 3, 'Qhat': 3}
def run_sel(a, edge):
    res = {}
    fs, R = forms(a)
    for name, (prods, posu1, negs) in fs.items():
        e = {m: F(0) for m in range(2 * a + 4)}
        for c, x, y in prods:
            for i in R:
                for j in R:
                    if x[i] * y[j] == 0: continue
                    W = i + j
                    if i in edge(W) or j in edge(W): e[W - 1] += c * x[i] * y[j]
        for c, l in posu1:
            for n, v in l.items(): e[n] += c * v
        for c, kind, l in negs:
            for n, v in l.items():
                if v == 0: continue
                if kind in ('u0', 'D'): e[n - 1] -= c * v
                if kind in ('u1', 'D'): e[n] -= c * v
        res[name] = [m for m, v in e.items() if v < 0]
    return res
for label, edge in [('i or j in {1,2,3}', lambda W: {1, 2, 3}), ('i or j in {1,2}', lambda W: {1, 2}), ('i or j in {1}', lambda W: {1})]:
    fails = {}
    for a in range(3, amax + 1):
        for name, bad in run_sel(a, edge).items():
            key = 'Q_s' if name.startswith('Q') and name != 'Qhat' else name
            if a < A0.get(key, 6 if key == 'Q_s' else 3): continue
            if key == 'Q_s' and a < 3: continue
            if bad: fails.setdefault(key, set()).add(a)
    print(label, {k: sorted(v)[:10] for k, v in fails.items()} or 'all pass')
