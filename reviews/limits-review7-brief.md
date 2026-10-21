# Review round 7: terminal-row correction (scoped)

You reviewed this paper in six rounds; round 6 (commit 0c9d8ffaef525b1f3551bf5e0eeb63f927eae0ef) returned PASS for Proposition 8.12, Corollary 8.13, the remark after Corollary 8.13 and two Section 9 sentences. After that the author tested whether the terminal-row heuristic could be made a theorem and found that it cannot be done as planned, and that the heuristic "transition at r = 1/2" was misleading. The source changed in exactly two passages of paper.tex (diff below) and the companion script fixedr_probe.py gained checks 5 and 6.

Current source: commit b65fcad90449f619aa7cd757551b570f5e24d668 (repository github.com/skypher/szkraw), paper.tex SHA-256 b36bd81d1a05be97a8a5127c3dd048e738e13649ad2234bbf3ad4be954c2c6b8.

Please check:
1. Are the new statements in the remark after Corollary 8.13 correct and properly scoped? In particular: (a) along the terminal row (c_N -> c_N + e, b_N -> b_N - e, all other coefficients fixed) g(N,N;N) is a polynomial in e because the linearization recurrence divides only by a_0, ..., a_{N-1}; (b) the four exact failures (sizes 6.3e-6 at r = 1/2, N = 120; 3.2e-3 at r = 2/5, N = 100; 1.6e-2 at r = 1/3, N = 120) satisfy the basic conditions and give g(N,N;N) < 0 (please recompute independently if you can); (c) the qualitative statement about Taylor coefficients is stated as a computational observation only.
2. Is the replacement Section 9 sentence accurate and not overstated?
3. Do the changes introduce any inconsistency with the rest of Sections 7-9 (for example other places that still suggest a threshold at r = 1/2 for finite perturbations)?
4. Verdict for the two changed passages: PASS, PASS WITH MINOR FIXES, or FAIL. Give replacement text for any fix.

Keep the answer short if everything is in order.

## Diff of paper.tex and fixedr_probe.py against the round-6 PASS version (9b2f5e4, which differs from 0c9d8ff only in the AI-use disclosure)

```diff
diff --git a/fixedr_probe.py b/fixedr_probe.py
index b670809..abf2a2e 100644
--- a/fixedr_probe.py
+++ b/fixedr_probe.py
@@ -14,6 +14,10 @@ Checks:
 4. Raising the top mass of K(N,r) to (1+tau) w_0 (exact for every tau): g(N,N;N) =
    [(1+tau)^2 (I - w_0) + w_0] / [(1+tau)(h - w_0) + w_0], I = (r(1-r))^N, h = r^N, w_0 = (r/(1+r))^N,
    negative exactly for tau > tau* = (1 - (1-r^2)^N)^(-1/2) - 1; the array moves by at most 3 tau max_n w_n.
+5. Along the terminal row g(N,N;N) is a polynomial in the perturbation e (the recurrence divides only by a_0..a_{N-1}).
+   Growth rates of its Taylor coefficients |g_k|, k = 1..4, at r = 1/2 (envelope over windows of six consecutive N,
+   N = 30..77): the rate increases with k, so r = 1/2 is a threshold for the first-order term only.
+6. Exact terminal-row failures at and below r = 1/2: g(N,N;N) < 0 at the stated e, with all basic conditions.
 """
 import argparse
 import math
@@ -46,6 +50,29 @@ def corner(a, b, c):
         prev, cur = cur, nxt
     return cur[N]
 
+def corner_poly(N, r):
+    """g(N,N;N) at K(N,r) with c_N -> c_N + e, b_N -> b_N - e, as exact coefficients in e."""
+    def add(p, q):
+        return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(max(len(p), len(q)))]
+    def mul(p, q):
+        out = [F(0)]*(len(p) + len(q) - 1)
+        for i, x in enumerate(p):
+            for j, y in enumerate(q): out[i+j] += x*y
+        return out
+    a, b, c = krawr(N, r)
+    B = [[x] for x in b]; C = [[x] for x in c]
+    B[N] = [b[N], F(-1)]; C[N] = [c[N], F(1)]
+    prev = [[F(0)] for _ in range(N+1)]; cur = [[F(int(i == N))] for i in range(N+1)]
+    for m in range(N):
+        nxt = []
+        for i in range(N+1):
+            v = add(mul(add(B[i], [-x for x in B[m]]), cur[i]), [-x for x in mul(C[m], prev[i])])
+            if i: v = add(v, mul(C[i], cur[i-1]))
+            if i < N: v = add(v, [a[i]*x for x in cur[i+1]])
+            nxt.append([x/a[m] for x in v])
+        prev, cur = cur, nxt
+    return cur[N]
+
 def raised_top(N, r, tau):
     from symmetric_probe import recurrence_from_measure, kraw_measure
     x, w = kraw_measure(N, r); w = list(w); w0 = w[0]; w[0] += tau*w0
@@ -96,6 +123,24 @@ def main():
         e1, g1, d1, b1 = check_raised(N, r, lo); e2, g2, d2, b2 = check_raised(N, r, hi)
         print(f'4. N={N} r={r}: tau*={tstar:.3e}; formula exact {e1 and e2}; corner at 0.99 tau* {float(g1):+.2e}, at 1.01 tau* {float(g2):+.2e}; '
               f'distance <= 3 tau max w_n: {d1 and d2}; diagonal >= 0: {b1 and b2}', flush=True)
+    r, W = F(1, 2), 6
+    logs = []
+    for N in range(30, 78):
+        p = corner_poly(N, r)
+        logs.append([math.log(abs(float(p[k]))) for k in range(1, 5)])
+    rates = []
+    for k in range(4):
+        env = [max(range(i, i+W), key=lambda j: logs[j][k]) for i in range(0, len(logs) - W + 1, W)]
+        rates.append(math.exp((logs[env[-1]][k] - logs[env[0]][k])/(env[-1] - env[0])))
+    print('5. r=1/2: growth rates of the Taylor coefficients g_1..g_4 in N: ' + ', '.join(f'{x:.3f}' for x in rates)
+          + ' (g(N,N;N) = (1/2)^N)', flush=True)
+    for N, r, e in ((120, F(1, 2), F(-63, 10**7)), (120, F(1, 2), F(-5, 10**6)), (100, F(2, 5), F(-32, 10**4)),
+                    (120, F(1, 3), F(-16, 10**3))):
+        a, b, c = krawr(N, r); b, c = list(b), list(c)
+        c[N] += e; b[N] -= e
+        basic = (all(x > 0 for x in a[:N]) and all(x >= 0 for x in b) and all(x > 0 for x in c[1:])
+                 and all(a[n] + b[n] + c[n] == 1 for n in range(N+1)))
+        print(f'6. N={N} r={r} e={float(e):.1e}: basic conditions {basic}; g(N,N;N) = {float(corner(a, b, c)):+.3e}', flush=True)
 
 if __name__ == '__main__':
     main()
diff --git a/paper.tex b/paper.tex
index edb7af7..fe64460 100644
--- a/paper.tex
+++ b/paper.tex
@@ -871,7 +871,7 @@ Put $x=(1-r^2)^N$ and $W=\max_nw_n$. For $0<x\leq\tfrac12$,
 so $\tau_N^*<x$. Choose $\tau\in(\tau_N^*,x)$. Proposition~\ref{prop:raise} gives a negative corner coefficient and full-array distance at most $3\tau W<3x\leq(1-r)/N$. Thus $\widetilde b_n>0$ for $n\geq1$, while $\widetilde b_0=0$. The exact coefficient formulas and the positive affine scale give $\widetilde a_n>0$ for $n<N$, $\widetilde c_n>0$ for $n>0$, and all the basic boundary and row-sum equalities. Letting $\tau\downarrow\tau_N^*$ proves $\rho_N(r)\leq3\tau_N^*W\leq3x$. For each fixed $r\in(0,1)$, both smallness conditions hold for all sufficiently large $N$, since $N(1-r^2)^N\to0$.
 \end{proof}
 
-Thus, for every fixed $r$, no set of arrays with property (P) contains coefficient balls of a radius independent of $N$ around all $K_{N,r}$; Theorem~\ref{thm:perturbation} gives the lower bound $\rho_N(r)\geq\tfrac12(\min(r,1-r)/(32N))^N$. The deformation of Proposition~\ref{prop:raise} has the binomial profile $w_n$ and is not a uniform rule. Along the terminal row alone, the first-order change of $g(N,N;N)$ at $K_{N,r}$ has an exact contour-integral representation, obtained as in Lemma~\ref{lem:corner} with $R_N(J)$ having eigenvalues $(-r)^j$. The formal saddle contributions have exponential factor $(1-r+r^2)/(1+r)$, which exceeds $1-r$ exactly when $r>\tfrac12$. For $r>\tfrac12$ this suggests an oscillatory first-order envelope, not a proved threshold for finite perturbations. No asymptotic estimate or uniform control of the nonlinear remainder is proved here. Exact computations (\path{fixedr_probe.py}) confirm failures of property (P) along the terminal row at sizes down to $10^{-15}$ for $r=4/5$, $N=40$.
+Thus, for every fixed $r$, no set of arrays with property (P) contains coefficient balls of a radius independent of $N$ around all $K_{N,r}$; Theorem~\ref{thm:perturbation} gives the lower bound $\rho_N(r)\geq\tfrac12(\min(r,1-r)/(32N))^N$. The deformation of Proposition~\ref{prop:raise} has the binomial profile $w_n$ and is not a uniform rule. Along the terminal row alone, the first-order change of $g(N,N;N)$ at $K_{N,r}$ has an exact contour-integral representation, obtained as in Lemma~\ref{lem:corner} with $R_N(J)$ having eigenvalues $(-r)^j$. The formal saddle contributions have exponential factor $(1-r+r^2)/(1+r)$, which exceeds $1-r$ exactly when $r>\tfrac12$. For $r>\tfrac12$ this suggests an oscillatory first-order envelope, not a proved threshold for finite perturbations. No asymptotic estimate or uniform control of the nonlinear remainder is proved here. Exact computations (\path{fixedr_probe.py}) confirm failures of property (P) along the terminal row at sizes down to $10^{-15}$ for $r=4/5$, $N=40$. The comparison at $r=\tfrac12$ concerns only the first-order term. Along the terminal row, $g(N,N;N)$ is a polynomial in the perturbation, since the recurrence for the linearization coefficients divides only by $a_0,\ldots,a_{N-1}$. In the same computations its second and higher Taylor coefficients decay more slowly in $N$ than the first, and the exact terminal-row failures continue for $r\leq\tfrac12$: at size $6.3\cdot10^{-6}$ for $r=\tfrac12$, $N=120$; at size $3.2\cdot10^{-3}$ for $r=\tfrac25$, $N=100$; and at size $1.6\cdot10^{-2}$ for $r=\tfrac13$, $N=120$.
 
 \paragraph{Computations away from $r=1$.}
 The explicit fixed-size, one-kink, and log-concave-increment examples below are reproduced by \path{rigidity_probe.py} and \path{smallr_probe.py}. Exact rational computations certify the stated finite examples; the separately labelled high-precision calculations provide numerical evidence. No asymptotic conclusion is asserted. Here $g(N,N;N)$ is computed from column $N$ of the product table, an $O(N^2)$-operation recurrence, so sizes in the hundreds are cheap.
@@ -900,7 +900,7 @@ For fixed $N$ and $0<r<1$, determine or estimate the largest coefficient radius
 At $r=1$, the reference margin in Lemma~\ref{lem:margin} vanishes because parity forces many coefficients to be zero. Symmetric perturbations preserve the parity zeros, and Theorem~\ref{thm:symmetric} exploits this for Szwarc's quadratic system when $p_0<1/2$. At $p_0=1/2$, and for the symmetric Krawtchouk array, further coefficients on the parity support vanish. Determine perturbation directions and structural constraints that preserve positivity there; continuity alone does not control coefficients emerging from those zeros. For every $N\geq1$, the symmetric Krawtchouk array is a limit of arrays whose product coefficients are strictly positive throughout the triangle support. For $N\geq2$ this follows from Proposition~\ref{prop:interior}; the two-point case is immediate. Theorem~\ref{thm:uniform} and Corollary~\ref{cor:analytic-rules} impose two boundary equalities on admitted polynomial rules and on the analytic rules satisfying the holomorphic-extension hypothesis specified there. A description of the cone for all $N$ is open.
 
 \paragraph{Monotonicity-type criteria for finite systems.}
-Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. For finite systems, property (P) at the boundary point is the hypergroup property of the corresponding birth--death chain, and Miclo~\cite[Theorem~31 and Proposition~6]{miclo2015} adapts the wave-equation argument of Bakry and Huet to give inequality conditions for chains that are symmetric under $n\mapsto N-n$ and sufficiently convex. These conditions do not cover the full Krawtchouk or Szwarc families. For symmetric Krawtchouk they fail when $N>2$, but the cases $N=1,2$ are covered; the Szwarc instance $N=1$, $p_0=1/2$ is the same covered three-point system. By Theorem~\ref{thm:decomp}, any criterion of this kind for nonsymmetric finite systems, valid including the terminal indices, immediately gives one for symmetric finite systems. Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$; the remaining task is to control these deep triples by inequalities that contain the geometric criterion. Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$. These examples show that the stated shape restrictions do not guarantee positivity at the specified biases and sizes. Each failure is witnessed by a negative terminal coefficient $g(N,N;N)$. Section~\ref{sec:limits} explains part of this: admission at the symmetric endpoint imposes two first-order boundary equalities for the polynomial rules of Theorem~\ref{thm:uniform} and the analytic rules of Corollary~\ref{cor:analytic-rules}, and the computational discussion there gives counterexamples to convex-profile conditions and to convex-profile conditions with log-concave increments at the stated parameters and sizes. Two questions remain. First, Corollary~\ref{cor:radius-exp} gives an exponential upper bound on the admissible coefficient-ball radius around $K_{N,r}$ for every fixed $r\in(0,1)$, witnessed by raising the top mass. Determine whether analogous upper bounds hold for terminal-row perturbations, and which uniform rules exhibit such thinness, when $r\in(\tfrac12,1)$; the remark after that corollary gives only heuristic evidence for a transition at $r=\tfrac12$. Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. Szwarc-type certificates were also tested on the deep triples. Floating-point linear-programming searches returned feasible backward-cone certificates for every deep triple in the tested Krawtchouk arrays. For some triples, the joint search for one coefficient-independent weight at $r=1/5$ and $r=1/2$ was reported infeasible. These numerical findings concern the specified certificate construction; no exact infeasibility certificates or general exclusion of linear-inequality criteria are supplied. Checkerboard-restricted searches did not certify all deep triples at the tested $r<1$. The exact marching calculations also produced examples with negative boundary flux. On the tested random perturbed arrays, the solver's certificate-feasibility results agreed with property (P).
+Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. For finite systems, property (P) at the boundary point is the hypergroup property of the corresponding birth--death chain, and Miclo~\cite[Theorem~31 and Proposition~6]{miclo2015} adapts the wave-equation argument of Bakry and Huet to give inequality conditions for chains that are symmetric under $n\mapsto N-n$ and sufficiently convex. These conditions do not cover the full Krawtchouk or Szwarc families. For symmetric Krawtchouk they fail when $N>2$, but the cases $N=1,2$ are covered; the Szwarc instance $N=1$, $p_0=1/2$ is the same covered three-point system. By Theorem~\ref{thm:decomp}, any criterion of this kind for nonsymmetric finite systems, valid including the terminal indices, immediately gives one for symmetric finite systems. Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$; the remaining task is to control these deep triples by inequalities that contain the geometric criterion. Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$. These examples show that the stated shape restrictions do not guarantee positivity at the specified biases and sizes. Each failure is witnessed by a negative terminal coefficient $g(N,N;N)$. Section~\ref{sec:limits} explains part of this: admission at the symmetric endpoint imposes two first-order boundary equalities for the polynomial rules of Theorem~\ref{thm:uniform} and the analytic rules of Corollary~\ref{cor:analytic-rules}, and the computational discussion there gives counterexamples to convex-profile conditions and to convex-profile conditions with log-concave increments at the stated parameters and sizes. Two questions remain. First, Corollary~\ref{cor:radius-exp} gives an exponential upper bound on the admissible coefficient-ball radius around $K_{N,r}$ for every fixed $r\in(0,1)$, witnessed by raising the top mass. Determine whether analogous upper bounds hold for terminal-row perturbations, and which uniform rules exhibit such thinness. The first-order comparison in the remark after that corollary changes at $r=\tfrac12$. The exact terminal-row failures reported there for $r\leq\tfrac12$ show that higher-order terms matter, so this comparison does not locate a threshold for finite perturbations. Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. Szwarc-type certificates were also tested on the deep triples. Floating-point linear-programming searches returned feasible backward-cone certificates for every deep triple in the tested Krawtchouk arrays. For some triples, the joint search for one coefficient-independent weight at $r=1/5$ and $r=1/2$ was reported infeasible. These numerical findings concern the specified certificate construction; no exact infeasibility certificates or general exclusion of linear-inequality criteria are supplied. Checkerboard-restricted searches did not certify all deep triples at the tested $r<1$. The exact marching calculations also produced examples with negative boundary flux. On the tested random perturbed arrays, the solver's certificate-feasibility results agreed with property (P).
 
 \paragraph{Other finite families.}
 Find analogous coefficient regions around other finite orthogonal systems and compare their geometry with the Krawtchouk neighborhoods. An algebra with a positive basis may supply the reference margin, but a recurrence criterion must express the resulting admissible deformations without requiring the unknown product coefficients as input.
```

## Output of the new checks (python3 fixedr_probe.py, items 5 and 6)

```
5. r=1/2: growth rates of the Taylor coefficients g_1..g_4 in N: 0.503, 0.593, 0.640, 0.676 (g(N,N;N) = (1/2)^N)
6. N=120 r=1/2 e=-6.3e-06: basic conditions True; g(N,N;N) = -2.865e-37
6. N=120 r=1/2 e=-5.0e-06: basic conditions True; g(N,N;N) = +1.826e-37
6. N=100 r=2/5 e=-3.2e-03: basic conditions True; g(N,N;N) = -6.328e-23
6. N=120 r=1/3 e=-1.6e-02: basic conditions True; g(N,N;N) = -8.485e-21
```

Context: K_{N,r} has a_n = 1 - n/N, b_n = (1-r)n/N, c_n = r n/N (fixedr_probe.py imports krawr from rigidity_probe.py); g(N,N;N) = (1-r)^N at K_{N,r}. The function corner() in fixedr_probe.py computes g(N,N;N) by the paper's linearization recurrence in exact rational arithmetic.
