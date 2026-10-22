"""Symbolic check of the boundary reductions in the proof of (eq:quad-B):
configuration u_0 = z, u_k = q^(k-1) (k >= 1); rho(l+1) = p, Delta rho(l) = s = t + tau*l.
(i) z = 1/q, h = 1 + 1/q: F(q) / (q^n (1+q)) = K A B - L p C.
(ii) z = l, q = 1/(l+w): F(q)/q^(n+1) = E_n(w) (n >= 3), E_2(w) - 12 A tau w (l+w)^2 (n = 2), and the coefficients."""
import sympy as sp
p, s, tau, q, l, w, z = sp.symbols('p s tau q ell w z', nonnegative=True)
def rho_at(k):  # rho(l + 1 + k) in terms of p, s, tau: Delta rho(l+m) = s + tau*m
    return p + sum(s + tau * m for m in range(1, k + 1))
def drho(m):  # Delta rho(l + m)
    return s + tau * m
def u(k, zz, qq):
    return zz if k == 0 else (qq ** (k - 1) if k >= 1 else 0)
def phi(n, base, uu):  # base = 0 for l, 1 for l+1; rho(l + base + n)
    r_ = rho_at(base + n - 1); dr = drho(base + n - 1); 
    return r_ * uu(n) + n * dr * (uu(n - 1) if n >= 1 else 0) + sp.Rational(n * (n - 1), 2) * tau * (uu(n - 2) if n >= 2 else 0)
ok = True
for n in range(2, 9):
    K = (n + 1) * (n + 2); L = 8 * (n - 1)
    for case in ['i', 'ii']:
        if case == 'i':
            zz = 1 / q
        else:
            zz = l
        U = lambda k: u(k, zz, q)
        U1 = lambda k: (u(k, zz, q) + u(k + 1, zz, q)) if k >= 0 else 0
        Fq = K * phi(2, 0, U) * phi(n, 1, U1) - L * p * (zz + 1) * phi(n + 2, 0, U)
        if case == 'i':
            h = 1 + 1 / q
            A = p + (2 * h - 1) * s + h ** 2 * tau
            B = p + n * h * (s + tau) + sp.Rational(n * (n - 1), 2) * h ** 2 * tau
            C = p + ((n + 2) * h - 1) * s + sp.Rational((n + 2) * (n + 1), 2) * h ** 2 * tau
            diff = sp.simplify(Fq / (q ** n * (1 + q)) - (K * A * B - L * p * C))
            if diff != 0: ok = False; print('case i fails', n, diff)
        else:
            h0 = l + 1; h = h0 + w
            A = p + (2 * h - 1) * s + tau * ((l + 2) * h - l - 1)
            B = p + n * h * (s + tau) + sp.Rational(n * (n - 1), 2) * h ** 2 * tau
            C = p + ((n + 2) * h - 1) * s + sp.Rational((n + 2) * (n + 1), 2) * h ** 2 * tau
            E = K * (h0 + w) * A * B - L * h0 * p * C
            target = E if n >= 3 else E - 12 * A * tau * w * (l + w) ** 2
            val = sp.simplify((Fq / q ** (n + 1)).subs(q, 1 / (l + w)) - target)
            if val != 0: ok = False; print('case ii fails', n, sp.factor(val))
            # coefficients in w (express t = s - tau*l)
            poly = sp.Poly(sp.expand(target), w)
            co = dict(zip([m[0] for m in poly.monoms()], poly.coeffs()))
            A0 = A.subs(w, 0); B0 = B.subs(w, 0); Ab = A0 - p; Bb = B0 - p
            eta = 2 * s + (l + 2) * tau; th = n * (s + tau) + n * (n - 1) * tau * h0; eps = sp.Rational(n * (n - 1), 2) * tau
            t = sp.symbols('t', nonnegative=True)
            if n >= 3:
                kk = n - 3
                P_ = 3*kk**3+15*kk**2+6*kk+8; Q_ = 6*kk**3+30*kk**2+20*kk+16; R_ = 3*kk**3+15*kk**2+16*kk+16
                a1 = (n+2)*(2*l*(n**2-n+6)+2*n**2-3*n+11); a2 = K*(n+2)
                b1 = sp.Rational(n+2, 2)*(l**2*P_+l*Q_+R_); b2 = sp.Rational(K, 2)*(3*n*(n-3)*(l+1)+14*l+12)
                claims = {1: K*p**2 + p*(a1*t + b1*tau) + K*(Ab*Bb + h0*(eta*Bb + Ab*th)),
                          2: p*(a2*t + b2*tau) + K*(eta*Bb + Ab*th + h0*(eta*th + Ab*eps)),
                          3: K*(eta*th + A0*eps + h0*eta*eps), 4: K*eta*eps}
            else:
                claims = {1: 12*p**2 + 4*(16*l+13)*p*t + 8*(l+1)*(2*l+3)*p*tau + 48*(l+1)*(3*l+2)*t**2
                              + 12*(36*l**3+92*l**2+76*l+21)*t*tau + 12*(27*l**4+93*l**3+114*l**2+62*l+13)*tau**2,
                          2: 48*p*t + 12*(2*l+3)*p*tau + 24*(6*l+5)*t**2 + 12*(36*l**2+67*l+29)*t*tau + 12*(27*l**3+78*l**2+67*l+19)*tau**2,
                          3: 12*(2*s+(l+2)*tau)*(2*t+(3*l+5)*tau), 4: sp.Integer(0)}
            for k_, cl in claims.items():
                got = co.get(k_, 0)
                if sp.expand(got - cl.subs(t, s - tau * l)) != 0:
                    ok = False; print('coef mismatch n=%d w^%d' % (n, k_), sp.factor(sp.expand(got - cl.subs(t, s - tau*l))))
print('ALL OK' if ok else 'MISMATCHES')
