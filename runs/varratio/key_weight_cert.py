"""Weight-sum certificates for the quadratic forms of the key inequality for all a.
Each form F has negative coefficients only at index pairs (0,W), (1,W-1), so its Abel tail criterion reduces to the
weight sums N_W(F) >= 0 (coefficients of F at u_n = r^n). For W >= 3 they have closed forms
   N_W = P_F * C(2a-1,W) + C(a,W-1) * rho_F(a,W)        (rho_F rational),
verified against the coefficient expansions by the scratch checks recorded in RESEARCH.md.
Forms: K'' and Q_s (lemma L1'), Ka, Psi, Qh (S_{2,0}), R, R2 (lemma L2).
Certificate:
 * W >= a+2: every negative term vanishes;
 * 6 <= W <= a+1: C(2a-1,W) >= sum_{k in {W,W-1,W-2,W-3,0,1,2}} C(a,k)C(a-1,W-k) (Vandermonde, disjoint k);
   with a = W-1+x, W = 6+y the cleared numerator of the lower bound must have nonnegative coefficients in (x,y);
 * 3 <= W <= 5: N_W is a polynomial in a; after a -> a + amin its coefficients must be nonnegative.
Usage: key_weight_cert.py"""
import sympy as sp
a, W, x, y = sp.symbols('a W x y', nonnegative=True)
s = sp.symbols('s', positive=True)
# binomials relative to c = C(a, W-1)
cW = (a - W + 1) / W; cW2 = (W - 1) / (a - W + 2); cW3 = (W - 1) * (W - 2) / ((a - W + 2) * (a - W + 3))
m1W = (a - W + 1) * (a - W) / (a * W); m1W1 = (a - W + 1) / a; m1W2 = (W - 1) / a
m2W2 = (W - 1) * (a - W + 1) / (a * (a - 1)); m2W3 = (W - 1) * (W - 2) / (a * (a - 1))
m3W3 = (W - 1) * (W - 2) * (a - W + 1) / (a * (a - 1) * (a - 2)); m3W4 = (W - 1) * (W - 2) * (W - 3) / (a * (a - 1) * (a - 2))
V = cW + (a - 1) + cW2 * (a - 1) * (a - 2) / 2 + cW3 * (a - 1) * (a - 2) * (a - 3) / 6 + m1W + a * m1W1 + a * (a - 1) / 2 * m1W2
YXneg = 2 * cW + 2 * m1W + 2 * a * m1W1 + 1 + (a - 1) * m1W2          # YX_W = 2C(2a-1,W) - c*YXneg
H0 = (W - 2) * cW; H1 = (W - 3)                                        # H_W / c, H_{W-1} / c
G1_0 = a * ((a - 1) * m2W2 - m1W1); G1_1 = a * ((a - 1) * m2W3 - m1W2)
G2_0 = a * (a - 1) / 2 * (a - 2) * m3W3; G2_1 = a * (a - 1) / 2 * (a - 2) * m3W4
def Gs0(sv):  # C(a,s)[(s-2) C(a-s,W-s) + (a-s) C(a-s-1,W-s-1)] / c, only used symbolically for s = 3 bound
    return None
c2 = (a - 1) * (a - 2) / 2
forms = {  # name: (P_F, rho_F, amin)
    "K''": (2, -YXneg - 4 * (H0 + H1), 3),
    'Ka': (2 * (a - 1), -(a - 1) * YXneg - 4 * a * (H0 + H1), 5),
    'Psi': (a, a * (-2 * cW - (a - 1)) - 2 * c2, 3),
    'Qh': (2 * (a - 1), -(a - 1) * YXneg - 4 * a * H0 + 2 * G1_0 + 4 * G2_0 - 4 * ((a + a * (a - 1) / 2) * H1 - G1_1 - G2_1), 3),
    'R': (a, a * (-2 * cW - 1) - 8 * (H0 + H1), 3),
    'R2': (a - 2, -(a - 2) * 2 * cW - 4 * a * (H0 + H1), 6),
    # Q_s of (L1'), crude form valid for every s >= 3 (G-term dropped, s = 3 in the negative terms), divided by c'
    'Q_s(crude)': (2, -YXneg - 4 * H0 - (sp.Rational(2, 3) * a - 2 + sp.Rational(4, 3) * a * (W - 3)), 3),
}
ok = True
for name, (P, rho, amin) in forms.items():
    expr = sp.together((P * V + rho).subs(a, W - 1 + x).subs(W, 6 + y))
    num, den = sp.fraction(expr)
    num = sp.expand(num); den = sp.factor(den)
    pn = sp.Poly(num, x, y); negc = [c for c in pn.coeffs() if c < 0]
    dpos = all(c > 0 for c in sp.Poly(sp.expand(den), x, y).coeffs())
    print(f"{name}: W >= 6 Vandermonde certificate: numerator has {len(negc)} negative coefficients; denominator positive: {dpos}")
    ok &= not negc and dpos
print('all W >= 6 certificates pass:', ok)

# ---- cross-check of the ratio forms against the integer closed forms, and small weights W = 3, 4, 5 ----
import math
from fractions import Fraction as Fr
Ci = lambda n, k: math.comb(n, k) if 0 <= k <= n else 0
def YXi(A, w): return 2*Ci(2*A-1, w) - 2*Ci(A, w) - 2*Ci(A-1, w) - 2*A*Ci(A-1, w-1) - Ci(A, w-1) - (A-1)*Ci(A-1, w-2)
def Hi(A, w): return (w - 2) * Ci(A, w) if w >= 3 else 0
def G1i(A, w): return A*((A-1)*Ci(A-2, w-2) - Ci(A-1, w-1))
def G2i(A, w): return Ci(A, 2) * (A-2) * Ci(A-3, w-3)
c2i = lambda A: Ci(A-1, 2)
integer_forms = {
    "K''": lambda A, w: YXi(A, w) - 4*(Hi(A, w) + Hi(A, w-1)),
    'Ka': lambda A, w: (A-1)*YXi(A, w) - 4*A*(Hi(A, w) + Hi(A, w-1)),
    'Psi': lambda A, w: A*(Ci(2*A-1, w) - 2*Ci(A, w) - (A-1)*Ci(A, w-1)) - 2*c2i(A)*Ci(A, w-1) + (c2i(A)*(A-1) if w == 3 else 0),
    'Qh': lambda A, w: (A-1)*YXi(A, w) - 4*A*Hi(A, w) + 2*G1i(A, w) + 4*G2i(A, w) - 4*((A + Ci(A, 2))*Hi(A, w-1) - G1i(A, w-1) - G2i(A, w-1)),
    'R': lambda A, w: A*(Ci(2*A-1, w) - 2*Ci(A, w) - Ci(A, w-1)) - 8*(Hi(A, w) + Hi(A, w-1)),
    'R2': lambda A, w: (A-2)*(Ci(2*A-1, w) - 2*Ci(A, w)) - 4*A*(Hi(A, w) + Hi(A, w-1)),
    'Q_s(crude)': lambda A, w: YXi(A, w) - 4*Hi(A, w) - Ci(A, w-1)*(Fr(2*A-6, 3) + Fr(4*A*(w-3), 3)),
}
mism = 0
for name, (P, rho, amin) in forms.items():
    f = sp.lambdify((a, W), rho)
    for A in range(6, 26):
        for w in range(4, A + 2):
            exact = integer_forms[name](A, w)
            ratio = sp.sympify(P).subs(a, sp.Integer(A)) * Ci(2*A-1, w) + Ci(A, w-1) * rho.subs({a: sp.Integer(A), W: sp.Integer(w)})
            if sp.simplify(ratio - exact) != 0: mism += 1
print('ratio-form vs integer closed form mismatches (4 <= W <= a+1, 6 <= a <= 25):', mism)
allsmall = True
for name, (P, rho, amin) in forms.items():
    for w in (3, 4, 5):
        if name == 'Q_s(crude)' and w == 3: continue   # W = 3 of Q_s is exact and handled by hand
        Ab = sp.symbols('A')
        bin_ = lambda n, k: sp.expand_func(sp.binomial(n, k)) if k >= 0 else 0
        def Cs(n, k): return sp.expand(sp.ff(n, k) / sp.factorial(k)) if k >= 0 else 0
        YX = 2*Cs(2*a-1, w) - 2*Cs(a, w) - 2*Cs(a-1, w) - 2*a*Cs(a-1, w-1) - Cs(a, w-1) - (a-1)*Cs(a-1, w-2)
        H = lambda k: (k - 2) * Cs(a, k) if k >= 3 else 0
        G1 = lambda k: a*((a-1)*Cs(a-2, k-2) - Cs(a-1, k-1))
        G2 = lambda k: a*(a-1)/2 * (a-2) * Cs(a-3, k-3)
        c2s = (a-1)*(a-2)/2
        poly = {"K''": YX - 4*(H(w) + H(w-1)), 'Ka': (a-1)*YX - 4*a*(H(w) + H(w-1)),
                'Psi': a*(Cs(2*a-1, w) - 2*Cs(a, w) - (a-1)*Cs(a, w-1)) - 2*c2s*Cs(a, w-1) + (c2s*(a-1) if w == 3 else 0),
                'Qh': (a-1)*YX - 4*a*H(w) + 2*G1(w) + 4*G2(w) - 4*((a + a*(a-1)/2)*H(w-1) - G1(w-1) - G2(w-1)),
                'R': a*(Cs(2*a-1, w) - 2*Cs(a, w) - Cs(a, w-1)) - 8*(H(w) + H(w-1)),
                'R2': (a-2)*(Cs(2*a-1, w) - 2*Cs(a, w)) - 4*a*(H(w) + H(w-1)),
                'Q_s(crude)': YX - 4*H(w) - Cs(a, w-1)*(sp.Rational(2, 3)*a - 2 + sp.Rational(4, 3)*a*(w-3))}[name]
        for A in range(max(amin, 3), 12): assert poly.subs(a, A) == integer_forms[name](A, w), (name, w, A)
        sh = sp.Poly(sp.expand(poly.subs(a, a + amin)), a)
        good = all(c >= 0 for c in sh.coeffs())
        allsmall &= good
        print(f'  {name} W={w}: N_W(a+{amin}) coefficients all >= 0: {good}' + ('' if good else f'  {sp.factor(poly)}'))
print('all small-weight checks pass:', allsmall)
assert ok and allsmall and mism == 0, 'weight certificate FAILED'
