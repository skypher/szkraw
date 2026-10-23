"""Symbolic per-n certificates for the edge u1-linearization of the key forms of Theorem 8.16.
Coefficient sequences are written for generic n (n >= 4) as multiples of C(a,n) with a = n + k (k >= 0):
  C(a,n+1) = C k/(n+1), C(a,n-1) = C n/(k+1), C(a,n-2) = C n(n-1)/((k+1)(k+2)), C(a-1,n) = C k/a,
  C(a-1,n-1) = C n/a, C(a-1,n-2) = C n(n-1)/(a(k+1)), C(a-1,n-3) = C n(n-1)(n-2)/(a(k+1)(k+2)).
Edge bound for a product of u0-free nonnegative forms x, y: coefficient of u1*u_n is
  x1*y_n + x2*y_{n-1} + y1*x_n[n>=3] + y2*x_{n-1}[n-1>=3].
Negatives: c*D*h -> -(c h_n + c h_{n+1}); c*u0*h -> -c h_{n+1}; c*u1*h -> -c h_n.
For each form, the cleared numerator of e_n / C(a,n) as a polynomial in (p, k) with n = 4 + p, and its sign pattern;
also the exact values for n = 1, 2, 3 as functions of a. Usage: edge_cert.py"""
import sympy as sp
n, k, p, a_, s = sp.symbols('n k p a s', nonnegative=True)
a = n + k
Cn = 1  # C(a,n) normalized
def cA(off):   # C(a, n+off) / C(a,n)
    return {0: 1, 1: k / (n + 1), -1: n / (k + 1), -2: n * (n - 1) / ((k + 1) * (k + 2)), 2: k * (k - 1) / ((n + 1) * (n + 2))}[off]
def cA1(off):  # C(a-1, n+off) / C(a,n)
    return {0: k / a, -1: n / a, -2: n * (n - 1) / (a * (k + 1)), -3: n * (n - 1) * (n - 2) / (a * (k + 1) * (k + 2)), 1: k * (k - 1) / (a * (n + 1))}[off]
# coefficient sequences as functions of the offset (generic n >= 4, index n+off >= 3)
seq = {
 'AmD': lambda o: cA(o), 'X': lambda o: cA(o), 'Xp': lambda o: cA1(o), 'Xpp': lambda o: cA1(o),
 'Y': lambda o: cA(o), 'Yp': lambda o: cA(o), 'J': lambda o: cA1(o),
 'H': lambda o: (n + o - 2) * cA(o),
}
first = {  # (x1, x2) of each positive sequence, as functions of a
 'AmD': (a - 1, a * (a - 1) / 2), 'X': (a, a * (a - 1) / 2), 'Xp': (a - 2, (a - 1) * (a - 2) / 2),
 'Xpp': (a - 1, (a - 1) * (a - 2) / 2), 'Y': (0, a * (a - 1) / 2), 'Yp': (0, (a - 1) * (a - 2) / 2), 'J': (0, (a - 1) * (a - 2) / 2)}
def prod_edge(xn, yn):  # coefficient of u1 u_n (generic n>=4)
    x1, x2 = first[xn]; y1, y2 = first[yn]
    return x1 * seq[yn](0) + x2 * seq[yn](-1) + y1 * seq[xn](0) + y2 * seq[xn](-1)
def lin_combo(pairs):
    return sum(c * prod_edge(x, y) for c, x, y in pairs)
H = seq['H']
def Zs(o, ss):  # Z_s coefficient at index n+o: (m-2)(C(a,s)-C(m,s))C(a,m), m = n+o -- keep symbolic s via ratio? use s=3 bound
    return None
forms = {
 'K':   lin_combo([(1, 'X', 'Yp'), (1, 'Y', 'Xp')]) - 4 * (H(0) + H(1)),
 'L':   lin_combo([(a - 2, 'AmD', 'X'), (a, 'AmD', 'Xp')]) - 4 * (H(0) + H(1)),
 'R':   lin_combo([(a, 'AmD', 'Xp')]) - 8 * (H(0) + H(1)),
 'R2':  lin_combo([(a - 2, 'AmD', 'Xpp')]) - 4 * a * (H(0) + H(1)),
 "K''": lin_combo([(1, 'Yp', 'Xpp'), (1, 'Y', 'Xp')]) - 4 * (H(0) + H(1)),
 'Ka':  (a - 1) * lin_combo([(1, 'Yp', 'Xpp'), (1, 'Y', 'Xp')]) - 4 * a * (H(0) + H(1)),
 'Psi': lin_combo([(a, 'AmD', 'J')]) - ((a - 1) * (a - 2) / 2) * (cA(0) + cA(0) + 0),
}
for name, e in forms.items():
    num, den = sp.fraction(sp.together(sp.simplify(e)))
    P = sp.Poly(sp.expand(num.subs(n, 4 + p)), p, k)
    neg = [(m, c) for m, c in zip(P.monoms(), P.coeffs()) if c < 0]
    print(f'{name}: denominator {sp.factor(den)}; numerator (n = 4+p): {len(P.coeffs())} terms, negative {neg[:6]}')
