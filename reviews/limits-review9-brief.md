# Confirmation round: your round-8 fixes

Your round-8 report (quoted below) gave PASS for item 1 and PASS WITH MINOR FIXES for item 2 (the Section 9 nonconvexity passage). The author applied your replacements verbatim and corrected the t-formula as you gave it, in paper.tex and in the convexity_probe.py docstring. Please confirm on the exact current source (commit 32c448808da5c8832da7bd62a2a78db39a532f34, repository github.com/skypher/szkraw, paper.tex SHA-256 a2d66cc1076ac8484fe06d21da679f5e853050b95577e9e780d5958958abce57):
1. Is each fix applied correctly?
2. Did the changes introduce any new error?
3. Final verdict for the Section 9 passage: PASS, PASS WITH MINOR FIXES, or FAIL.

Keep the answer short if everything is in order.

## Your round-8 report

## Item 1: PASS

The correction is present as quoted in the cited commit. It correctly separates the finite-range decay observation from the exact terminal-row failures. No further change is needed. [1]

## Item 2: PASS WITH MINOR FIXES

**The computations check out, but the displayed \(t\)-formula is wrong and the conclusion needs tighter scope.**

### Algebra

Writing \(d_i=b_i+c_i\), the mixture has
\[
d_i=(1-\lambda)\frac{i}{N}+\lambda\frac{[i]_q}{[N]_q}.
\]
Thus stochasticity, \(b_0=c_0=0\), and \(b_i/c_i=(1-r)/r\) for \(i\ge1\) all hold. Its increments satisfy
\[
d_i-d_{i-1}
=\frac{1-\lambda}{N}+\frac{\lambda(q-1)q^{i-1}}{q^N-1}
=\frac{1-\lambda}{N}\left(1+tq^{i-N}\right),
\]
where the **correct** formula is
\[
\boxed{t=\frac{\lambda N(q-1)q^{N-1}}{(1-\lambda)(q^N-1)}}.
\]

Change “For \(0<\lambda<1\)” to “For \(q>1\) and \(0<\lambda<1\)” and replace the formula accordingly. The executable `combination()` already uses the correct inverse relationship; fix the docstring too. [2]

### Sign verification

I independently reproduced **all seven exact negative signs**, using an integer-scaled **row** recurrence rather than importing the supplied column routine. The three specifically requested checks give:

| \((r,N,q,t)\) | \(g(N,N;N)\), rounded |
|---|---:|
| \((4/5,10,10,1)\) | \(-6.966013504304\times10^{-4}\) |
| \((1/2,20,10,1)\) | \(-7.851192966406\times10^{-6}\) |
| \((2/5,60,10,2)\) | \(-6.659918540452\times10^{-10}\) |

I also independently reproduced the \(150\)- and \(300\)-digit results:
\[
\frac{g(500,500;500)}{(3/4)^{500}}
\approx-1.2454570392633845283487240314981492\times10^{23}.
\]
The “not an exact sign certificate” qualification is appropriate.

### Scope and replacement text

A simultaneous system of strict or non-strict linear inequalities is convex. The obstruction therefore applies to **sufficient criteria for (P)** containing both endpoints, at the **exactly certified parameter choices**—not automatically to the numerical \(N=500\) case.

Replace the opening nonconvexity claim with:
```tex
A criterion given by linear inequalities in the coefficients admits a
convex set of arrays, but the set of arrays satisfying property (P)
need not be convex, even at fixed $(N,r)$ and with both endpoints
admitted by Theorem~\ref{thm:criterion}.
```

Replace the “Hence” sentence with:
```tex
Hence, for each of the seven exactly certified parameter choices above,
no sufficient criterion for property (P) whose admitted set is convex,
in particular no sufficient criterion defined by a system of linear
inequalities in the coefficients, can admit both $K_{N,r}$ and
$G_{N,q,r}$.
```

Mirror this scope in the script docstring.

The final sentence is acceptably observational. To avoid implying an exhaustive search over every integer \(N\le1000\), sharpen it to:
```tex
In our searches, the sizes of the examples found tended to increase
as $r$ decreased; at $r=1/5$ no negative corner was found on the tested
$(N,q,t)$ grid with $N\leq1000$.
```
I did not independently rerun that scan; no minimal-size or asymptotic conclusion follows.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/d87857f4df168a32e3b619bb319551365ff4a838/paper.tex
[2] https://raw.githubusercontent.com/skypher/szkraw/d87857f4df168a32e3b619bb319551365ff4a838/convexity_probe.py


## Diff against the reviewed commit d87857f (paper.tex and convexity_probe.py)

```diff
diff --git a/convexity_probe.py b/convexity_probe.py
index 1013233..a4f9643 100644
--- a/convexity_probe.py
+++ b/convexity_probe.py
@@ -1,11 +1,12 @@
 """Nonconvexity of property (P) at fixed (N, r) (Section 9); exact, diagnostics.
 
 K(N,r) = G(N,1,r) and the geometric array G(N,q,r) of (eq:parameters), q > 1, are both admitted by Theorem 2.1
-(constant ratio b_i/c_i = (1-r)/r, geometric increments). The convex combination (1-lam) K + lam G is again a
-stochastic constant-ratio array with b_0 = 0; its increments are proportional to 1 + t q^(i-N), not geometric, where
-t = lam (q^N - 1)/((1-lam) N (q-1) q^(N-1)). For each listed (r, N, q, t) it has g(N,N;N) < 0 in exact arithmetic.
-So no criterion whose admitted set is convex, such as a system of linear inequalities in the coefficients, admits
-both K(N,r) and G(N,q,r) at these sizes.
+(constant ratio b_i/c_i = (1-r)/r, geometric increments). For 0 < lam < 1 the convex combination (1-lam) K + lam G
+is again a stochastic constant-ratio array with b_0 = 0; its increments are proportional to 1 + t q^(i-N), not
+geometric, where t = lam N (q-1) q^(N-1)/((1-lam) (q^N - 1)). For each listed (r, N, q, t) it has g(N,N;N) < 0 in
+exact arithmetic. So, for each of these exactly certified choices, no sufficient criterion for property (P) whose
+admitted set is convex, in particular none defined by linear inequalities in the coefficients, can admit both
+K(N,r) and G(N,q,r). The high-precision case below is not an exact certificate and is not covered by this claim.
 
 Option --all adds the exact cases (3/10, 200, 2, 5) and (2/7, 200, 10, 5) (about 1 and 6 minutes) and the case
 (1/4, 500, 3, 10) in 150- and 300-digit arithmetic (not an exact sign certificate). Option --scan R: high-precision
diff --git a/paper.tex b/paper.tex
index eb0de4e..4be6b1e 100644
--- a/paper.tex
+++ b/paper.tex
@@ -900,7 +900,7 @@ For fixed $N$ and $0<r<1$, determine or estimate the largest coefficient radius
 At $r=1$, the reference margin in Lemma~\ref{lem:margin} vanishes because parity forces many coefficients to be zero. Symmetric perturbations preserve the parity zeros, and Theorem~\ref{thm:symmetric} exploits this for Szwarc's quadratic system when $p_0<1/2$. At $p_0=1/2$, and for the symmetric Krawtchouk array, further coefficients on the parity support vanish. Determine perturbation directions and structural constraints that preserve positivity there; continuity alone does not control coefficients emerging from those zeros. For every $N\geq1$, the symmetric Krawtchouk array is a limit of arrays whose product coefficients are strictly positive throughout the triangle support. For $N\geq2$ this follows from Proposition~\ref{prop:interior}; the two-point case is immediate. Theorem~\ref{thm:uniform} and Corollary~\ref{cor:analytic-rules} impose two boundary equalities on admitted polynomial rules and on the analytic rules satisfying the holomorphic-extension hypothesis specified there. A description of the cone for all $N$ is open.
 
 \paragraph{Monotonicity-type criteria for finite systems.}
-Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. For finite systems, property (P) at the boundary point is the hypergroup property of the corresponding birth--death chain, and Miclo~\cite[Theorem~31 and Proposition~6]{miclo2015} adapts the wave-equation argument of Bakry and Huet to give inequality conditions for chains that are symmetric under $n\mapsto N-n$ and sufficiently convex. These conditions do not cover the full Krawtchouk or Szwarc families. For symmetric Krawtchouk they fail when $N>2$, but the cases $N=1,2$ are covered; the Szwarc instance $N=1$, $p_0=1/2$ is the same covered three-point system. By Theorem~\ref{thm:decomp}, any criterion of this kind for nonsymmetric finite systems, valid including the terminal indices, immediately gives one for symmetric finite systems. Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$; the remaining task is to control these deep triples by inequalities that contain the geometric criterion. Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$. These examples show that the stated shape restrictions do not guarantee positivity at the specified biases and sizes. Each failure is witnessed by a negative terminal coefficient $g(N,N;N)$. Section~\ref{sec:limits} explains part of this: admission at the symmetric endpoint imposes two first-order boundary equalities for the polynomial rules of Theorem~\ref{thm:uniform} and the analytic rules of Corollary~\ref{cor:analytic-rules}, and the computational discussion there gives counterexamples to convex-profile conditions and to convex-profile conditions with log-concave increments at the stated parameters and sizes. Two questions remain. First, Corollary~\ref{cor:radius-exp} gives an exponential upper bound on the admissible coefficient-ball radius around $K_{N,r}$ for every fixed $r\in(0,1)$, witnessed by raising the top mass. Determine whether analogous upper bounds hold for terminal-row perturbations, and which uniform rules exhibit such thinness. The first-order comparison in the remark after that corollary changes at $r=\tfrac12$. The exact terminal-row failures reported there for $r\leq\tfrac12$ show that higher-order terms matter, so this comparison does not locate a threshold for finite perturbations. Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. A criterion given by linear inequalities in the coefficients admits a convex set of arrays, but property (P) at fixed $(N,r)$ is not convex, even between arrays admitted by Theorem~\ref{thm:criterion}. For $q\geq1$ let $G_{N,q,r}$ be the array \eqref{eq:parameters}, so that $G_{N,1,r}=K_{N,r}$. For $0<\lambda<1$ the combination $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ is a stochastic array with constant ratio $b_i/c_i$ and increments proportional to $1+t\,q^{i-N}$, where $t=\lambda(q^N-1)/((1-\lambda)N(q-1)q^{N-1})$. Exact computation (\path{convexity_probe.py}) gives $g(N,N;N)<0$ for this combination at $(r,N,q,t)=(4/5,10,10,1)$, $(3/5,20,10,2)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$, $(1/3,100,10,2)$, $(3/10,200,2,5)$ and $(2/7,200,10,5)$. Computations in $150$- and $300$-digit arithmetic agree on $g(N,N;N)<0$ at $(1/4,500,3,10)$; this is not an exact sign certificate. Hence, at these sizes, no criterion whose admitted set is convex, in particular no system of linear inequalities in the coefficients, admits both $K_{N,r}$ and $G_{N,q,r}$. The sizes at which we found such failures grow as $r$ decreases; at $r=1/5$ none was found on our grid of values of $q$ and $t$ for $N\leq1000$. Szwarc-type certificates were also tested on the deep triples. Floating-point linear-programming searches returned feasible backward-cone certificates for every deep triple in the tested Krawtchouk arrays. For some triples, the joint search for one coefficient-independent weight at $r=1/5$ and $r=1/2$ was reported infeasible. These numerical findings concern the specified certificate construction; no exact infeasibility certificates or general exclusion of linear-inequality criteria are supplied. Checkerboard-restricted searches did not certify all deep triples at the tested $r<1$. The exact marching calculations also produced examples with negative boundary flux. On the tested random perturbed arrays, the solver's certificate-feasibility results agreed with property (P).
+Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. For finite systems, property (P) at the boundary point is the hypergroup property of the corresponding birth--death chain, and Miclo~\cite[Theorem~31 and Proposition~6]{miclo2015} adapts the wave-equation argument of Bakry and Huet to give inequality conditions for chains that are symmetric under $n\mapsto N-n$ and sufficiently convex. These conditions do not cover the full Krawtchouk or Szwarc families. For symmetric Krawtchouk they fail when $N>2$, but the cases $N=1,2$ are covered; the Szwarc instance $N=1$, $p_0=1/2$ is the same covered three-point system. By Theorem~\ref{thm:decomp}, any criterion of this kind for nonsymmetric finite systems, valid including the terminal indices, immediately gives one for symmetric finite systems. Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$; the remaining task is to control these deep triples by inequalities that contain the geometric criterion. Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$. These examples show that the stated shape restrictions do not guarantee positivity at the specified biases and sizes. Each failure is witnessed by a negative terminal coefficient $g(N,N;N)$. Section~\ref{sec:limits} explains part of this: admission at the symmetric endpoint imposes two first-order boundary equalities for the polynomial rules of Theorem~\ref{thm:uniform} and the analytic rules of Corollary~\ref{cor:analytic-rules}, and the computational discussion there gives counterexamples to convex-profile conditions and to convex-profile conditions with log-concave increments at the stated parameters and sizes. Two questions remain. First, Corollary~\ref{cor:radius-exp} gives an exponential upper bound on the admissible coefficient-ball radius around $K_{N,r}$ for every fixed $r\in(0,1)$, witnessed by raising the top mass. Determine whether analogous upper bounds hold for terminal-row perturbations, and which uniform rules exhibit such thinness. The first-order comparison in the remark after that corollary changes at $r=\tfrac12$. The exact terminal-row failures reported there for $r\leq\tfrac12$ show that higher-order terms matter, so this comparison does not locate a threshold for finite perturbations. Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. A criterion given by linear inequalities in the coefficients admits a convex set of arrays, but the set of arrays satisfying property (P) need not be convex, even at fixed $(N,r)$ and with both endpoints admitted by Theorem~\ref{thm:criterion}. For $q\geq1$ let $G_{N,q,r}$ be the array \eqref{eq:parameters}, so that $G_{N,1,r}=K_{N,r}$. For $q>1$ and $0<\lambda<1$ the combination $(1-\lambda)K_{N,r}+\lambda G_{N,q,r}$ is a stochastic array with constant ratio $b_i/c_i$ and increments proportional to $1+t\,q^{i-N}$, where $t=\lambda N(q-1)q^{N-1}/((1-\lambda)(q^N-1))$. Exact computation (\path{convexity_probe.py}) gives $g(N,N;N)<0$ for this combination at $(r,N,q,t)=(4/5,10,10,1)$, $(3/5,20,10,2)$, $(1/2,20,10,1)$, $(2/5,60,10,2)$, $(1/3,100,10,2)$, $(3/10,200,2,5)$ and $(2/7,200,10,5)$. Computations in $150$- and $300$-digit arithmetic agree on $g(N,N;N)<0$ at $(1/4,500,3,10)$; this is not an exact sign certificate. Hence, for each of the seven exactly certified parameter choices above, no sufficient criterion for property (P) whose admitted set is convex, in particular no sufficient criterion defined by a system of linear inequalities in the coefficients, can admit both $K_{N,r}$ and $G_{N,q,r}$. In our searches, the sizes of the examples found tended to increase as $r$ decreased; at $r=1/5$ no negative corner was found on the tested $(N,q,t)$ grid with $N\leq1000$. Szwarc-type certificates were also tested on the deep triples. Floating-point linear-programming searches returned feasible backward-cone certificates for every deep triple in the tested Krawtchouk arrays. For some triples, the joint search for one coefficient-independent weight at $r=1/5$ and $r=1/2$ was reported infeasible. These numerical findings concern the specified certificate construction; no exact infeasibility certificates or general exclusion of linear-inequality criteria are supplied. Checkerboard-restricted searches did not certify all deep triples at the tested $r<1$. The exact marching calculations also produced examples with negative boundary flux. On the tested random perturbed arrays, the solver's certificate-feasibility results agreed with property (P).
 
 \paragraph{Other finite families.}
 Find analogous coefficient regions around other finite orthogonal systems and compare their geometry with the Krawtchouk neighborhoods. An algebra with a positive basis may supply the reference margin, but a recurrence criterion must express the resulting admissible deformations without requiring the unknown product coefficients as input.
```
