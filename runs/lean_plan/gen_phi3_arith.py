"""Emit the Lean generic-index certificates eA_arith, eB_arith for the Phi3 edge forms of the cubic key
(n = p+4 <= a = p+4+K; c = C(a,n), cm = C(a,n-1), cp = C(a,n+1), cp2 = C(a,n+2), cp3 = C(a,n+3),
d = C(a-1,n-1), e = C(a-1,n)). EXPR mirrors lean/Szkraw/CubicKeyForms.lean at the generic index; checks
EXPR = c NUM / DEN with NUM having nonnegative coefficients. Usage: gen_phi3_arith.py OUT"""
import sys, sympy as sp
p, K, c, cm, cp, cp2, cp3, d, e = sp.symbols('p K c cm cp cp2 cp3 d e')
A = '(p + 4 + K)'
s = f'({A} - 1) * ({A} - 2) / 2'
c3a = f'{A} * ({A} - 1) * ({A} - 2) / 6'
c3a1 = f'({A} - 1) * ({A} - 2) * ({A} - 3) / 6'
def C3(x): return f'({x}) * (({x}) - 1) * (({x}) - 2) / 6'
nn = '(p + 4)'
H0 = f'(({nn} - 2) * c)'
H1 = f'(({nn} + 1 - 2) * cp)'
T3 = f'(({nn} - 2) * c * ({c3a} - {C3(nn)}))'
W = lambda k, atom: f'(({nn} + {k} - 2) * {atom} * {C3(f"{nn} + {k}")})'
E3 = f'(3 * {W(1, "cp")} + 3 * {W(2, "cp2")} + {W(3, "cp3")})'
eYX = f'(0 * e + {A} * ({A} - 1) / 2 * d + ({A} - 2) * c + ({A} - 1) * ({A} - 2) / 2 * cm)'
eXY = f'({A} * c + {A} * ({A} - 1) / 2 * cm + 0 * c + ({A} * ({A} - 1) / 2 - ({A} - 1)) * cm)'
forms = {
  'eA': f'{s} * {eYX} - {c3a1} * c - 4 * {T3} + {E3}',
  'eB': f'{s} * ({eXY} + {eYX}) - 4 * {s} * ({H0} + {H1}) - {c3a} * c - {c3a1} * c - 4 * {T3} + {E3}',
}
sub = {cm: c * (p + 4) / (K + 1), cp: c * K / (p + 5), cp2: c * K * (K - 1) / ((p + 5) * (p + 6)),
       cp3: c * K * (K - 1) * (K - 2) / ((p + 5) * (p + 6) * (p + 7)), d: c * (p + 4) / (p + 4 + K),
       e: c * K / (p + 4 + K)}
loc = {str(x): x for x in (p, K, c, cm, cp, cp2, cp3, d, e)}
out = []
for name, ex in forms.items():
    E = sp.sympify(ex, locals=loc)
    num, den = sp.fraction(sp.together(sp.expand(E.subs(sub) / c)))
    num, den = sp.expand(num), sp.factor(den)
    P = sp.Poly(num, p, K)
    assert all(co >= 0 for co in P.coeffs()), name
    l = sp.lcm([sp.fraction(co)[1] for co in P.coeffs()])
    num = sp.expand(num * l); den = sp.factor(den * l)
    numl = ' + '.join(str(co) + (' * ' + ' * '.join(f'{v} ^ {k}' for v, k in zip(('p', 'K'), mon) if k) if any(mon) else '')
                      for mon, co in zip(sp.Poly(num, p, K).monoms(), sp.Poly(num, p, K).coeffs()))
    denl = str(den).replace('**', '^')
    out.append(f'''theorem {name}_arith (p K c cm cp cp2 cp3 d e : ℝ) (hp : 0 ≤ p) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h1 : cm * (K + 1) = c * (p + 4)) (h2 : cp * (p + 5) = c * K) (h3 : d * (p + 4 + K) = c * (p + 4))
    (h4 : e * (p + 4 + K) = c * K) (h5 : cp2 * (p + 6) = cp * (K - 1)) (h6 : cp3 * (p + 7) = cp2 * (K - 2)) :
    0 ≤ {ex} := by
  have hK1 : 0 < K + 1 := by linarith
  have hp5 : 0 < p + 5 := by linarith
  have hp6 : 0 < p + 6 := by linarith
  have hp7 : 0 < p + 7 := by linarith
  have ha : 0 < p + 4 + K := by linarith
  have ecm : cm = c * (p + 4) / (K + 1) := by field_simp; linarith
  have ecp : cp = c * K / (p + 5) := by field_simp; linarith
  have ecp2 : cp2 = c * K * (K - 1) / ((p + 5) * (p + 6)) := by rw [ecp] at h5; field_simp at h5 ⊢; linarith
  have ecp3 : cp3 = c * K * (K - 1) * (K - 2) / ((p + 5) * (p + 6) * (p + 7)) := by
    rw [ecp2] at h6; field_simp at h6 ⊢; linarith
  have ed : d = c * (p + 4) / (p + 4 + K) := by field_simp; linarith
  have ee : e = c * K / (p + 4 + K) := by field_simp; linarith
  rw [ecm, ecp3, ecp2, ecp, ed, ee]
  have hN : 0 ≤ c * ({numl}) / ({denl}) := by positivity
  exact le_of_le_of_eq hN (by field_simp; ring)
''')
    print(name, 'terms', len(P.coeffs()), 'den', den, file=sys.stderr)
open(sys.argv[1], 'w').write('\n'.join(out))
