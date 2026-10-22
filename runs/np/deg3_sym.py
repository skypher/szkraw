"""Symbolic coefficients of Q = k^2 e_k^2 - (k^2-1) e_{k-1} e_{k+1} for degree-3 (NP), x = (s_{k-3},...,s_{k+1})."""
import sympy as sp
x = sp.symbols('x0:5'); n1, n2, n3, k = sp.symbols('n1 n2 n3 k')
A = lambda kk: n1 + (kk - 1) * n2 / 2 + (kk - 1) * (kk - 2) * n3 / 6
B = lambda kk: (kk - 1) * n2 / 2 + (kk - 1) * (kk - 2) * n3 / 3
C = lambda kk: (kk - 1) * (kk - 2) * n3 / 6
ek = A(k) * x[3] + B(k) * x[2] + C(k) * x[1]
ekm = A(k - 1) * x[2] + B(k - 1) * x[1] + C(k - 1) * x[0]
ekp = A(k + 1) * x[4] + B(k + 1) * x[3] + C(k + 1) * x[2]
Q = sp.Poly(sp.expand(k ** 2 * ek ** 2 - (k ** 2 - 1) * ekm * ekp), *x)
if __name__ == '__main__':
    for i in range(5):
        for j in range(i, 5):
            cf = sp.factor(Q.coeff_monomial(x[i] * x[j]))
            if cf != 0: print(f'x{i}x{j}:', cf)
