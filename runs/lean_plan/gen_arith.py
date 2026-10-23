"""Emit the Lean generic-index certificates `eR_arith`, `eR2_arith`, `ePsi_arith`, `eKa_arith`, `eQhat_arith`
(n = p+4 <= a = p+4+K; c = C(a,n), cm = C(a,n-1), cp = C(a,n+1), d = C(a-1,n-1), e = C(a-1,n)). Each EXPR is the
e_n of lean/Szkraw/GenFormR.lean at the generic index; checks EXPR = c NUM / DEN with NUM having nonnegative
coefficients in (p, K). Usage: gen_arith.py OUT"""
import sys, sympy as sp
p, K, c, cm, cp, d, e = sp.symbols('p K c cm cp d e')
A = '(p + 4 + K)'
POS = (f'(0 * e + ({A} * ({A} - 1) / 2 - ({A} - 1)) * d + ({A} - 1) * c + ({A} - 1) * ({A} - 2) / 2 * cm + '
       f'(0 * e + {A} * ({A} - 1) / 2 * d + ({A} - 2) * c + ({A} - 1) * ({A} - 2) / 2 * cm))')
H0, H1 = '((p + 4 - 2) * c)', '((p + 4 + 1 - 2) * cp)'
edge = lambda y1: f'(({A} - 1) * e + {A} * ({A} - 1) / 2 * d + {y1} * c + ({A} - 1) * ({A} - 2) / 2 * cm)'
forms = {
  'eR': f'{A} * {edge(f"({A} - 2)")} - 8 * {H0} - 8 * {H1}',
  'eR2': f'({A} - 2) * {edge(f"({A} - 1)")} - 4 * {A} * {H0} - 4 * {A} * {H1}',
  'ePsi': f'{A} * {edge("0")} - ({A} - 1) * ({A} - 2) / 2 * (c + c)',
  'eKa': f'({A} - 1) * {POS} - 4 * {A} * {H0} - 4 * {A} * {H1}',
  'eQhat': f'({A} - 1) * {POS} + (2 * ((p + 4) + 1) ^ 2 - 4 * {A}) * {H1} - '
           f'4 * ({A} + {A} * ({A} - 1) / 2 - (p + 4) - (p + 4) * ((p + 4) - 1) / 2) * {H0}',
}
sub = {cm: c * (p + 4) / (K + 1), cp: c * K / (p + 5), d: c * (p + 4) / (p + 4 + K), e: c * K / (p + 4 + K)}
out = []
for name, ex in forms.items():
    E = sp.sympify(ex.replace('^', '**'), locals={'p': p, 'K': K, 'c': c, 'cm': cm, 'cp': cp, 'd': d, 'e': e})
    num, den = sp.fraction(sp.together(sp.expand(E.subs(sub) / c)))
    num, den = sp.expand(num), sp.factor(den)
    P = sp.Poly(num, p, K)
    assert all(co >= 0 for co in P.coeffs()), name
    l = sp.lcm([sp.fraction(co)[1] for co in P.coeffs()])
    if l != 1: num, den = sp.expand(num * l), sp.factor(den * l)
    numl = ' + '.join(f'{co} * {"p ^ " + str(i) if i else ""}{" * " if i and j else ""}{"K ^ " + str(j) if j else ""}'.replace('* ', '* ', 1)
                      if (i or j) else f'{co}' for (i, j), co in zip(sp.Poly(num, p, K).monoms(), sp.Poly(num, p, K).coeffs()))
    numl = numl.replace(' * )', ')').replace('p ^ 1', 'p').replace('K ^ 1', 'K')
    denl = str(den).replace('**', '^')
    rwl = ', '.join(r for v, r in (('cm', 'ecm'), ('cp', 'ecp'), ('d', 'ed'), ('e', 'ee')) if sp.Symbol(v) in E.free_symbols)
    out.append(f'''theorem {name}_arith (p K c cm cp d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) :
    0 ≤ {ex} := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  have ee : e = c * K / (p + 4 + K) := by field_simp; linarith
  rw [{rwl}]
  have hN : 0 ≤ c * ({numl}) / ({denl}) := by positivity
  exact le_of_le_of_eq hN (by field_simp; ring)
''')
    print(name, 'den', den, 'terms', len(P.coeffs()))
open(sys.argv[1], 'w').write('\n'.join(out))
