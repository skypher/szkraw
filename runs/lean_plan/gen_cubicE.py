"""Generate the Lean certificate of the cubic E detour (Theorem 8.17, eq. cubic-E): for n >= 3,
3(n-1) c_{l+1} e_{n+2}(l) <= (n+1)(n+2) (phi_2(l) + (n/3) phi_3(l)) e_n(l+1), e from Lean `eCv`.
Derived from gen_cubicB.py (same Abel/tail certificate); there is no quadratic part to subtract.
Original B description follows.
Generate the Lean certificate of the cubic B detour (Theorem 8.17, eq. cubic-B) for one n-case.
D = (n+1)(n+2) phi_2(l) phi_n(l+1) - 8(n-1) c_{l+1} phi_{n+2}(l) is bilinear in rho = (r, t, tau, sigma), so
D = sum_{b <= c} rho_b rho_c kappa_bc with kappa_bc built from the basis ratios e_0 = 1, e_1 = x, e_2 = C(x,2),
e_3 = C(x,3) (Lean: PhiC 1 0 0 0, PhiC 0 1 0 0, ...). The quadratic part (rr, r tau, tau tau) is `quadB_seq`
(Theorem 8.11). For each remaining form (rt, tt, t sigma, tau sigma, sigma sigma, t tau, t tau + r sigma) we prove
kappa >= 0: group by index sum; in a group the monomials v_a v_{s-a} increase with a (log-concavity), and Abel
summation writes kappa = sum_k T_k (m_k - m_{k-1}) + T_{a0} m_{a0}, every tail T_k a polynomial in (l, m) with
nonnegative coefficients (asserted). The main theorem combines these with rho >= 0 and r sigma <= t tau through
(t tau - r sigma) kappa_ttau + r sigma (kappa_ttau + kappa_rsigma).
Usage: gen_cubicE.py CASE OUT   (CASE = gen | 3 | 4 | 5 | 6; gen is n = m + 7)"""
import sys, os
import sympy as sp

L, M = sp.symbols('l m', nonnegative=True)
CASE = sys.argv[1]
URS = sp.Rational(os.environ.get('URS', '7/4'))  # weight of kappa_rsigma in the combined form
GEN = CASE == 'gen'
n = M + 7 if GEN else sp.Integer(int(CASE))
lsym = L
BASIS = {'r': (1, 0, 0, 0), 't': (0, 1, 0, 0), 'tau': (0, 0, 1, 0), 'sig': (0, 0, 0, 1)}
LEANB = {'r': '1 0 0 0', 't': '0 1 0 0', 'tau': '0 0 1 0', 'sig': '0 0 0 1'}

def C2(x): x = sp.sympify(x); return x * (x - 1) * sp.Rational(1, 2)
def C3(x): x = sp.sympify(x); return x * (x - 1) * (x - 2) * sp.Rational(1, 6)
def rho(b, x):
    r, t, tau, sig = BASIS[b]; return r + t * x + tau * C2(x) + sig * C3(x)
def drho(b, x):
    r, t, tau, sig = BASIS[b]; return t + tau * x + sig * C2(x)
def d2rho(b, x):
    r, t, tau, sig = BASIS[b]; return tau + sig * x
def sigc(b): return BASIS[b][3]

V = {}
def v(idx):
    idx = sp.expand(idx)
    if idx.is_Integer and idx < 0: return 0
    if idx not in V: V[idx] = sp.Symbol('v_' + str(len(V)))
    return V[idx]
def ww(k): return v(k) + v(k + 1)
def phi(b, ll, k, vf):
    return rho(b, ll + k) * vf(k) + k * drho(b, ll + k - 1) * vf(k - 1) + C2(k) * d2rho(b, ll + k - 2) * vf(k - 2) \
        + C3(k) * sigc(b) * vf(k - 3)
K, Lc = (n + 1) * (n + 2), 3 * (n - 1)
EB = {'tau': (1, 0), 'sig': (0, 1)}
def ee(c, ll, k, vf):
    a, b = EB[c]
    return C2(k) * (a + b * ll) * vf(k - 2) + b * C3(k) * (3 * vf(k - 1) + 3 * vf(k - 2) + vf(k - 3))
def kap(b, c):
    ll = lsym
    e = K * (phi(b, ll, 2, v) + n / sp.Integer(3) * phi(b, ll, 3, v)) * ee(c, ll + 1, n, ww) \
        - Lc * rho(b, ll + 1) * (v(0) + v(1)) * ee(c, ll, n + 2, v)
    return sp.expand(e)

def lean_poly(e):
    e = sp.expand(e)
    if e == 0: return '0'
    return sp.sstr(e).replace('**', ' ^ ').replace('l', '(ℓ : ℝ)').replace('m', '(m : ℝ)')
def lean_idx(i):
    i = sp.expand(i)
    if i.has(M):
        k = sp.expand(i - M); return f'(m + {k})' if k != 0 else 'm'
    return str(i)
def sortkey(x): return (x.has(M), x if not x.has(M) else x - M)

def cert(expr):
    """Abel/tail certificate: list of (lean_statement, lean_proof)."""
    inv = {s: i for i, s in V.items()}
    syms = [s for s in V.values() if expr.has(s)]
    P = sp.Poly(expr, *syms)
    coef = {}
    for mon, c in zip(P.monoms(), P.coeffs()):
        ids = sorted([inv[syms[k]] for k, e in enumerate(mon) for _ in range(e)], key=sortkey)
        assert len(ids) == 2
        coef[tuple(ids)] = sp.expand(coef.get(tuple(ids), 0) + c)
    groups = {}
    for (a, b), c in coef.items():
        assert not a.has(M), 'small index expected first'
        groups.setdefault(sp.expand(a + b), {})[int(a)] = c
    facts = []
    for s, mem in sorted(groups.items(), key=lambda kv: str(kv[0])):
        a0, a1 = min(mem), max(mem)
        for k in range(a0, a1 + 1):
            T = sp.expand(sum(mem.get(a, 0) for a in range(k, a1 + 1)))
            if T == 0: continue
            for c in sp.Poly(T, L, M).coeffs(): assert c >= 0, ('negative tail coefficient', s, k, T)
            big = lambda j: lean_idx(sp.expand(s - j))
            if k == a0:
                facts.append((f'0 ≤ ({lean_poly(T)}) * (v {k} * v {big(k)})',
                              'mul_nonneg (by positivity) (mul_nonneg (hv.1 _) (hv.1 _))'))
            else:
                facts.append((f'0 ≤ ({lean_poly(T)}) * (v {k} * v {big(k)} - v {k - 1} * v {big(k - 1)})',
                              f'mul_nonneg (by positivity) (sub_nonneg.2 (hv.step (x := {k - 1}) (y := {lean_idx(sp.expand(s - k - 1))}) (by omega)))'))
    return facts

nl = '(m + 7)' if GEN else CASE
lv = 'ℓ'
lhyp = '(ℓ m : ℕ)' if GEN else '(ℓ : ℕ)'
Ktxt = f'((({nl} : ℕ) : ℝ) + 1) * ((({nl} : ℕ) : ℝ) + 2)'
Ltxt = f'3 * ((({nl} : ℕ) : ℝ) - 1)'
W = '(fun k => v k + v (k + 1))'
LEANE = {'tau': '1 0', 'sig': '0 1'}
def katom(b, c):
    B, Cc = LEANB[b], LEANE[c]
    return (f'{Ktxt} * ((PhiC {B} {lv} 2 v + ((({nl} : ℕ) : ℝ) / 3) * PhiC {B} {lv} 3 v) * eCv {Cc} ({lv} + 1) {nl} {W}) - '
            f'{Ltxt} * (rhoC {B} ({lv} + 1) * (v 0 + v 1) * eCv {Cc} {lv} ({nl} + 2) v)')
FORMS = {'rtau': [('r', 'tau')], 'ttau': [('t', 'tau')], 'tautau': [('tau', 'tau')], 'ts': [('t', 'sig')],
         'taus': [('tau', 'sig'), ('sig', 'tau')], 'ss': [('sig', 'sig')], 'ttaurs': [('t', 'tau'), ('r', 'sig')]}
SUF = {'gen': 'gen', '3': 'three', '4': 'four', '5': 'five', '6': 'six'}[CASE]
expand_lines = []
if GEN:
    expand_lines += ['  rw [show m + 7 + 2 = m + 6 + 3 by ring]', '  rw [show m + 7 = m + 4 + 3 by ring]',
                     '  simp only [PhiC_two, PhiC_three, eCv_add3, rhoC, drhoC, d2rhoC, choose2_real, choose3_real]']
else:
    expand_lines += ['  simp only [PhiC, eCv, rhoC, drhoC, d2rhoC, choose2_real, choose3_real]']
expand_lines += ['  push_cast', '  try simp only [Nat.add_assoc, Nat.reduceAdd]']
out = []
total = 0
for name, pairs in FORMS.items():
    expr = sp.expand(sum((URS if (b, c) == ('r', 'sig') else 1) * kap(b, c) for b, c in pairs))
    facts = cert(expr)
    total += len(facts)
    stmt = ' + '.join((f'({URS.p} / {URS.q} : ℝ) * ' if (b, c) == ('r', 'sig') else '') + f'({katom(b, c)})' for b, c in pairs)
    lines = [f'theorem kapE_{SUF}_{name} {{v : ℕ → ℝ}} (hv : LCNZ v) {lhyp} :', f'    0 ≤ {stmt} := by']
    for i, (st, pr) in enumerate(facts):
        lines.append(f'  have g{i} : {st} := {pr}')
    lines += expand_lines
    lines.append('  linear_combination ' + (' + '.join(f'g{i}' for i in range(len(facts))) if facts else '0'))
    out.append('\n'.join(lines))
# main theorem
A = '{"ℓ m" if GEN else "ℓ"}'
main = [f'theorem cubicE_{SUF} {{v : ℕ → ℝ}} (hv : LCNZ v) {{r t τ σ : ℝ}} (hr : 0 < r) (ht : 0 ≤ t)',
        f'    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hrs : r * σ ≤ t * τ) {lhyp} :',
        f'    {Ltxt} * (rhoC r t τ σ ({lv} + 1) * (v 0 + v 1) * eCv τ σ {lv} ({nl} + 2) v) ≤',
        f'      {Ktxt} * ((PhiC r t τ σ {lv} 2 v + ((({nl} : ℕ) : ℝ) / 3) * PhiC r t τ σ {lv} 3 v) * eCv τ σ ({lv} + 1) {nl} {W}) := by',
        f'  rw [PhiC_lin r t τ σ {lv} 2, PhiC_lin r t τ σ {lv} 3, rhoC_lin r t τ σ ({lv} + 1), eCv_lin τ σ {lv} ({nl} + 2),',
        f'    eCv_lin τ σ ({lv} + 1) {nl}]',
        f'  have c1 := mul_nonneg (mul_nonneg hr.le hτ) (kapE_{SUF}_rtau hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c2 := mul_nonneg (mul_nonneg hτ hτ) (kapE_{SUF}_tautau hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c3 := mul_nonneg (mul_nonneg ht hσ) (kapE_{SUF}_ts hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c4 := mul_nonneg (mul_nonneg hτ hσ) (kapE_{SUF}_taus hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c5 := mul_nonneg (mul_nonneg hσ hσ) (kapE_{SUF}_ss hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c6 := mul_nonneg (by linarith : (0 : ℝ) ≤ t * τ - r * σ) (kapE_{SUF}_ttau hv {"ℓ m" if GEN else "ℓ"})',
        f'  have c7 := mul_nonneg (mul_nonneg hr.le hσ) (kapE_{SUF}_ttaurs hv {"ℓ m" if GEN else "ℓ"})',
        f'  linear_combination c1 + c2 + c3 + c4 + c5 + c6 + c7']
out.append('\n'.join(main))
open(sys.argv[2], 'w').write('\n\n'.join(out) + '\n')
print(f'case {CASE}: {total} tail facts', file=sys.stderr)
