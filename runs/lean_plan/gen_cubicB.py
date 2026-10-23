"""Generate the Lean certificate of the cubic B detour (Theorem 8.17, eq. cubic-B) for one n-case.
D = (n+1)(n+2) phi_2(l) phi_n(l+1) - 8(n-1) c_{l+1} phi_{n+2}(l) is bilinear in rho = (r, t, tau, sigma), so
D = sum_{b <= c} rho_b rho_c kappa_bc with kappa_bc built from the basis ratios e_0 = 1, e_1 = x, e_2 = C(x,2),
e_3 = C(x,3) (Lean: PhiC 1 0 0 0, PhiC 0 1 0 0, ...). The quadratic part (rr, r tau, tau tau) is `quadB_seq`
(Theorem 8.11). For each remaining form (rt, tt, t sigma, tau sigma, sigma sigma, t tau, t tau + r sigma) we prove
kappa >= 0: group by index sum; in a group the monomials v_a v_{s-a} increase with a (log-concavity), and Abel
summation writes kappa = sum_k T_k (m_k - m_{k-1}) + T_{a0} m_{a0}, every tail T_k a polynomial in (l, m) with
nonnegative coefficients (asserted). The main theorem combines these with rho >= 0 and r sigma <= t tau through
(t tau - r sigma) kappa_ttau + r sigma (kappa_ttau + kappa_rsigma).
CASE corner: (l, n) = (0, 2) with v_0 = 0, the inequality 8 c_1 phi_4(0) <= 12 (phi_2(0) + (2/3) phi_3(0)) phi_2(1)
(eq. cubic-corner); its quadratic part is quadB_seq plus the nonnegative extra term 8 phi_3(0) phi_2(1) at t = sigma = 0.
Usage: gen_cubicB.py CASE OUT   (CASE = gen | 2 | 3 | 4 | 5 | corner; gen is n = m + 6, case 2 is l >= 1)"""
import sys, os
import sympy as sp

L, M = sp.symbols('l m', nonnegative=True)
CASE = sys.argv[1]
URS = sp.Rational(os.environ.get('URS', '7/4'))  # weight of kappa_rsigma in the combined form
GEN = CASE == 'gen'
COR = CASE == 'corner'
n = M + 6 if GEN else sp.Integer(2 if COR else int(CASE))
lsym = L + 1 if CASE == '2' else (sp.Integer(0) if COR else L)
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
    if COR and idx == 0: return 0
    if idx not in V: V[idx] = sp.Symbol('v_' + str(len(V)))
    return V[idx]
def ww(k): return v(k) + v(k + 1)
def phi(b, ll, k, vf):
    return rho(b, ll + k) * vf(k) + k * drho(b, ll + k - 1) * vf(k - 1) + C2(k) * d2rho(b, ll + k - 2) * vf(k - 2) \
        + C3(k) * sigc(b) * vf(k - 3)
K, Lc = (n + 1) * (n + 2), 8 * (n - 1)
def kap(b, c):
    ll = lsym
    if COR:
        third = sp.Rational(2, 3)
        if b == c:
            return sp.expand(K * (phi(b, ll, 2, v) + third * phi(b, ll, 3, v)) * phi(b, ll + 1, n, ww)
                             - Lc * rho(b, ll + 1) * (v(0) + v(1)) * phi(b, ll, n + 2, v))
        return sp.expand(K * ((phi(b, ll, 2, v) + third * phi(b, ll, 3, v)) * phi(c, ll + 1, n, ww)
                              + (phi(c, ll, 2, v) + third * phi(c, ll, 3, v)) * phi(b, ll + 1, n, ww))
                         - Lc * (rho(b, ll + 1) * (v(0) + v(1)) * phi(c, ll, n + 2, v)
                                 + rho(c, ll + 1) * (v(0) + v(1)) * phi(b, ll, n + 2, v)))
    if b == c:
        e = K * phi(b, ll, 2, v) * phi(b, ll + 1, n, ww) - Lc * rho(b, ll + 1) * (v(0) + v(1)) * phi(b, ll, n + 2, v)
    else:
        e = K * (phi(b, ll, 2, v) * phi(c, ll + 1, n, ww) + phi(c, ll, 2, v) * phi(b, ll + 1, n, ww)) \
            - Lc * (rho(b, ll + 1) * (v(0) + v(1)) * phi(c, ll, n + 2, v) + rho(c, ll + 1) * (v(0) + v(1)) * phi(b, ll, n + 2, v))
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

nl = '(m + 6)' if GEN else ('2' if COR else CASE)
lv = '(ℓ + 1)' if CASE == '2' else ('0' if COR else 'ℓ')
lhyp = '(ℓ m : ℕ)' if GEN else ('(hv0 : v 0 = 0)' if COR else '(ℓ : ℕ)')
Ktxt = f'((({nl} : ℕ) : ℝ) + 1) * ((({nl} : ℕ) : ℝ) + 2)'
Ltxt = f'8 * ((({nl} : ℕ) : ℝ) - 1)'
W = '(fun k => v k + v (k + 1))'
def P2(B): return f'(PhiC {B} {lv} 2 v + ((2 : ℝ) / 3) * PhiC {B} {lv} 3 v)' if COR else f'PhiC {B} {lv} 2 v'
def katom(b, c):
    B, Cc = LEANB[b], LEANB[c]
    if COR:
        if b == c:
            return (f'{Ktxt} * {P2(B)} * PhiC {B} ({lv} + 1) {nl} {W} - '
                    f'{Ltxt} * rhoC {B} ({lv} + 1) * (v 0 + v 1) * PhiC {B} {lv} ({nl} + 2) v')
        return (f'{Ktxt} * ({P2(B)} * PhiC {Cc} ({lv} + 1) {nl} {W} + {P2(Cc)} * PhiC {B} ({lv} + 1) {nl} {W}) - '
                f'{Ltxt} * (rhoC {B} ({lv} + 1) * (v 0 + v 1) * PhiC {Cc} {lv} ({nl} + 2) v + '
                f'rhoC {Cc} ({lv} + 1) * (v 0 + v 1) * PhiC {B} {lv} ({nl} + 2) v)')
    if b == c:
        return (f'{Ktxt} * PhiC {B} {lv} 2 v * PhiC {B} ({lv} + 1) {nl} {W} - '
                f'{Ltxt} * rhoC {B} ({lv} + 1) * (v 0 + v 1) * PhiC {B} {lv} ({nl} + 2) v')
    return (f'{Ktxt} * (PhiC {B} {lv} 2 v * PhiC {Cc} ({lv} + 1) {nl} {W} + PhiC {Cc} {lv} 2 v * PhiC {B} ({lv} + 1) {nl} {W}) - '
            f'{Ltxt} * (rhoC {B} ({lv} + 1) * (v 0 + v 1) * PhiC {Cc} {lv} ({nl} + 2) v + '
            f'rhoC {Cc} ({lv} + 1) * (v 0 + v 1) * PhiC {B} {lv} ({nl} + 2) v)')
FORMS = {'rt': [('r', 't')], 'tt': [('t', 't')], 'ts': [('t', 'sig')], 'taus': [('tau', 'sig')],
         'ss': [('sig', 'sig')], 'ttau': [('t', 'tau')], 'ttaurs': [('t', 'tau'), ('r', 'sig')]}
SUF = {'gen': 'gen', '2': 'two', '3': 'three', '4': 'four', '5': 'five', 'corner': 'corner'}[CASE]
expand_lines = []
if GEN:
    expand_lines += ['  rw [show m + 6 + 2 = m + 5 + 3 by ring]', '  rw [show m + 6 = m + 3 + 3 by ring]',
                     '  simp only [PhiC_two, PhiC_add3, rhoC, drhoC, d2rhoC, choose2_real, choose3_real]']
else:
    expand_lines += ['  simp only [PhiC, rhoC, drhoC, d2rhoC, choose2_real, choose3_real]']
expand_lines += ['  push_cast', '  try simp only [Nat.add_assoc, Nat.reduceAdd]']
if COR: expand_lines += ['  simp only [hv0]']
out = []
total = 0
for name, pairs in FORMS.items():
    expr = sp.expand(sum((URS if (b, c) == ('r', 'sig') else 1) * kap(b, c) for b, c in pairs))
    facts = cert(expr)
    total += len(facts)
    stmt = ' + '.join((f'({URS.p} / {URS.q} : ℝ) * ' if (b, c) == ('r', 'sig') else '') + f'({katom(b, c)})' for b, c in pairs)
    lines = [f'theorem kapB_{SUF}_{name} {{v : ℕ → ℝ}} (hv : LCNZ v) {lhyp} :', f'    0 ≤ {stmt} := by']
    for i, (st, pr) in enumerate(facts):
        lines.append(f'  have g{i} : {st} := {pr}')
    lines += expand_lines
    lines.append('  linear_combination ' + (' + '.join(f'g{i}' for i in range(len(facts))) if facts else '0'))
    out.append('\n'.join(lines))
# main theorem
ARG = 'ℓ m' if GEN else ('hv0' if COR else 'ℓ')
hz_l = f'(({lv} : ℕ) : ℝ)'
P2r = f'(PhiC r t τ σ {lv} 2 v + ((2 : ℝ) / 3) * PhiC r t τ σ {lv} 3 v)' if COR else f'PhiC r t τ σ {lv} 2 v'
main = [f'theorem cubicB_{SUF} {{v : ℕ → ℝ}} (hv : LCNZ v) (hv1 : 0 < v 1) {{r t τ σ : ℝ}} (hr : 0 < r) (ht : 0 ≤ t)',
        f'    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hrs : r * σ ≤ t * τ) {lhyp} (hz : v 0 ≤ {hz_l} * v 1) :',
        f'    {Ltxt} * rhoC r t τ σ ({lv} + 1) * (v 0 + v 1) * PhiC r t τ σ {lv} ({nl} + 2) v ≤',
        f'      {Ktxt} * {P2r} * PhiC r t τ σ ({lv} + 1) {nl} {W} := by',
        f'  have hq := quadB_seq (v := v) hv hv1 (n := {nl}) (by norm_num) hr le_rfl hτ (Nat.cast_nonneg _) hz',
        f'  rw [show ({hz_l} + 1) = ((({lv} + 1 : ℕ) : ℝ)) by push_cast; ring] at hq',
        f'  rw [PhiQ_zero_eq, PhiQ_zero_eq, PhiQ_zero_eq, rhoQ_zero_eq] at hq',
        f'  rw [PhiC_lin r 0 τ 0 {lv} ({nl} + 2), PhiC_lin r 0 τ 0 {lv} 2, PhiC_lin r 0 τ 0 ({lv} + 1) {nl},',
        f'    rhoC_lin r 0 τ 0 ({lv} + 1)] at hq',
        f'  rw [PhiC_lin r t τ σ {lv} ({nl} + 2), PhiC_lin r t τ σ {lv} 2, PhiC_lin r t τ σ ({lv} + 1) {nl},',
        f'    rhoC_lin r t τ σ ({lv} + 1)' + (f', PhiC_lin r t τ σ {lv} 3]' if COR else ']'),
        f'  have c1 := mul_nonneg (mul_nonneg hr.le ht) (kapB_{SUF}_rt hv {ARG})',
        f'  have c2 := mul_nonneg (mul_nonneg ht ht) (kapB_{SUF}_tt hv {ARG})',
        f'  have c3 := mul_nonneg (mul_nonneg ht hσ) (kapB_{SUF}_ts hv {ARG})',
        f'  have c4 := mul_nonneg (mul_nonneg hτ hσ) (kapB_{SUF}_taus hv {ARG})',
        f'  have c5 := mul_nonneg (mul_nonneg hσ hσ) (kapB_{SUF}_ss hv {ARG})',
        f'  have c6 := mul_nonneg (by linarith : (0 : ℝ) ≤ t * τ - r * σ) (kapB_{SUF}_ttau hv {ARG})',
        f'  have c7 := mul_nonneg (mul_nonneg hr.le hσ) (kapB_{SUF}_ttaurs hv {ARG})',
        f'  linear_combination hq + c1 + c2 + c3 + c4 + c5 + c6 + c7' + (' + cq' if COR else '')]
if COR:
    main.insert(-1, f'  have cq : 0 ≤ {Ktxt} * (((2 : ℝ) / 3) * (r * PhiC 1 0 0 0 0 3 v + 0 * PhiC 0 1 0 0 0 3 v + τ * PhiC 0 0 1 0 0 3 v + 0 * PhiC 0 0 0 1 0 3 v)) * (r * PhiC 1 0 0 0 (0 + 1) 2 {W} + 0 * PhiC 0 1 0 0 (0 + 1) 2 {W} + τ * PhiC 0 0 1 0 (0 + 1) 2 {W} + 0 * PhiC 0 0 0 1 (0 + 1) 2 {W}) := by')
    main.insert(-1, f'    rw [← PhiC_lin, ← PhiC_lin]; have h3 := PhiC_nonneg hr.le le_rfl hτ le_rfl hv.1 0 3; have h2 := PhiC_nonneg hr.le le_rfl hτ le_rfl (fun k => add_nonneg (hv.1 k) (hv.1 (k + 1))) (0 + 1) 2; positivity')
out.append('\n'.join(main))
open(sys.argv[2], 'w').write('\n\n'.join(out) + '\n')
print(f'case {CASE}: {total} tail facts', file=sys.stderr)
