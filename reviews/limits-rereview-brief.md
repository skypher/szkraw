# Follow-up referee review: corrected Sections 7 and 8

You reviewed Sections 7 and 8 of this paper before (verdict FAIL; your full report is quoted below). The author has revised the paper. The corrected LaTeX source follows your report (repository skypher/szkraw, commit 4381af5ae43b4b94f62dd49dd8c98f9e4067142c, paper.tex SHA-256 2af3459bdb7e4d541ab9c697ef210880112030307131ceb7c186054ce0d4d65b).

Please act again as an independent referee. Do not trust the author.
1. For each defect in your report, check whether the revision fixes it correctly and completely.
2. Read the revised Sections 7 and 8 (and the revised sentences in the introduction and Section 9) in full. Check every new or changed statement and proof, including any new error introduced by the revision.
3. Two points where the author deviated from your suggestions; judge them:
   - Fixed-N interior claim: the author did not adopt your general argument ("decreasing the mass at x=1 ... adding a sufficiently large multiple of the Krawtchouk direction"). Their reason: at odd-parity structural zeros with excess at least 3 (for example (N,N,N) with N odd), the symmetric mass change keeps b identically zero, so the first-order change there is zero, and so is that of the Krawtchouk direction (it vanishes to order equal to the excess). The sentence was therefore restricted to the computed sizes N <= 10. Is this objection to your argument correct?
   - The paragraph after Corollary 7.9 now keeps the Lemma 7.5 transfer, with the condition on Sigma that you gave and your K_{2,1} example (checked exactly by the author: g(2,2;2) = -2 eps/(1/2 - eps)).
4. The author rechecked exactly before using them: your Szwarc reversal value g'(2,2;2) = (2p_0-1)/(N p_0) (N = 3, 4; p_0 = 1/3, 2/5) and your values 512/1875 (N = 4) and -71936/5859375 (N = 8) at r = 4/5.

Output format: an overall verdict (PASS, PASS WITH MINOR FIXES, or FAIL); a table with one row per defect from your first report (fixed / partly fixed / not fixed, with a reason); then any new defects, with exact location and replacement text.

## Your first report

# 1. Overall verdict: **FAIL**

The principal positivity results in Section 7, the corner identity in Lemma 8.2, the polynomial-rule obstruction in Theorem 8.4, and the fixed-\(N\) stability-radius order in Corollary 8.9 are mathematically sound, subject to the corrections below.

However, the manuscript is not correct as written. Corollary 8.6 overstates the analytic extension; Proposition 8.7(1) has an ambiguous fixed-sign hypothesis whose usual weak interpretation makes it false; several surrounding claims exceed the proved obstruction; and the asserted period-four signs away from \(r=1\) are contradicted by exact computation.

I independently reconstructed the main identities and performed exact checks, rather than relying on the author’s diagnostics. A reproducible, standard-library-only check script is available here: [referee_checks.py](sandbox:/mnt/data/referee_checks.py).

# 2. Result-by-result table

| Result | Verdict | Reason |
|---|---|---|
| Theorem 7.1 — Szwarc’s quadratic system | **correct** | The positive-module argument handles every finite product; \(g(2,2;2)=(1-r)/N\), including \(N=1\). |
| Lemma 7.2 — Edge idempotents | **correct** | The idempotent identities, basis independence, and positivity of the projection are valid. |
| Lemma 7.3 — Three-term action | **correct** | Both counting identities hold, including \(YU_0=U_1\) and \(YU_{2N}=U_{2N-1}\). |
| Lemma 7.4 — Quadratic margin | **correct** | The mixed-product support construction and norm-ratio estimate give the stated conservative margin. |
| Lemma 7.5 — Stability with a margin | **correct** | The error recurrence is valid; its conclusion is only positivity on \(\Sigma\), not automatically full property (P). |
| Theorem 7.6 — Symmetric neighborhood | **correct** | The radius preserves all required signs; symmetry preserves the parity zeros. |
| Corollary 7.7 — Outside both families | **correct** | For \(N\ge2\), \(c_1>c_3\) excludes both specified families. |
| Theorem 7.8 — Quadratic decomposition | **correct** | The normalized component arrays, their supports, and the mixed-product formula are correct for \(N\ge2\). |
| Corollary 7.9 — Parity-split criterion | **correct with fixable gap** | Positivity and sharpness hold, but the claimed odd-component parametrization is undefined when \(N=1\). |
| Theorem 7.10 — Low products | **correct** | Direct calculation of \(H^*v\) confirms the four boundary/interior expressions and their stated index ranges. |
| Corollary 7.11 — Convex profiles | **correct** | Convexity gives \(d_i+d_j\le d_{i+j}\); the low-product hypotheses follow. |
| Lemma 7.12 — Reversal identity | **correct with fixable gap** | The identity is valid, but the reversed initial normalization must be stated explicitly. |
| Theorem 7.13 — Deep reduction | **correct** | Both expansion identities and the final use of triple-product symmetry are valid. |
| Theorem 7.14 — Palindromic criterion | **correct** | Reversal coincides with the original system, so the deep reduction applies. |
| Corollary 7.15 — Monotone palindromic systems | **correct** | Its assumptions imply the basic positivity conditions and all hypotheses of Theorem 7.14. |
| Lemma 8.1 — Corner value | **correct** | The coefficient of \(y_1\cdots y_N\) in its square is exactly \((1-r)^N\). |
| Lemma 8.2 — Corner identity | **correct** | Independent derivation confirms the eigenvector normalization, signs, beta integrals, and terminal contribution. |
| Definition 8.3 — Uniform rule | **correct with fixable gap** | Specify real-valued functions and whether the small-\(\varepsilon\) threshold may depend on \(N\). |
| Theorem 8.4 — Forced equalities | **correct** | Polynomial finite differences vanish above the degree; the alternating signs force both boundary functionals to vanish. |
| Lemma 8.5 — Nörlund–Rice bound | **correct with fixable gap** | The bound is valid; the contour construction and its uniform separation from \([0,1]\) should be supplied. |
| Corollary 8.6 — Analytic rules | **incorrect** | Only the necessary-equality conclusion extends. Exact first-order vanishing does not extend to general analytic functions. |
| Proposition 8.7 — \(N\)-dependent families | **unclear** | Part (1) is false if “constant sign” permits zeros; part (2) is correct after replacing the argument. |
| Proposition 8.8 — Thinness | **correct** | Rational dependence gives a smooth extension and a uniform negative derivative in a small rectangle. |
| Corollary 8.9 — Radius order | **correct with fixable gap** | The conclusion is correct; the proof should use the full recurrence-array norm and explicitly verify admissibility. |

# 3. Independent verification and required corrections

## A. Section 7: the main arguments work

### Graded construction, margins, and terminal cases

The two action identities are
\[
YU_{2n}=\frac{N-n}{N}U_{2n+1}+\frac nN U_{2n-1},
\qquad
YU_{2n+1}=\frac{U_{2n+2}+rU_{2n}}{1+r}.
\]
They include both endpoints without introducing an undefined polynomial.

The proof of Theorem 7.1 correctly uses an \(A\)-module, not an unstated multiplication on all of \(V\). When one factor is even, the product becomes multiplication by a nonnegative element of \(A\). When both factors are odd, triple-product symmetry transfers the sign question to an even–odd product. The terminal polynomial annihilates \(U_0\), so this argument remains valid beyond the terminating degree.

The sharpness calculation is also valid for \(N=1\):
\[
g(2,2;2)=\frac{1-r}{N}.
\]

For Lemma 7.4, I obtain
\[
\pi_{2a}=\binom Na r^{-a},
\qquad
\pi_{2c+1}=\frac{\binom{N-1}{c}r^{-c}}{p_0}.
\]
The ratio in the odd–odd argument has the correct orientation:
\[
g(2b+1,2c+1;2a)
=
g(2a,2b+1;2c+1)\frac{\pi_{2a}}{\pi_{2c+1}}.
\]
The resulting lower bound indeed dominates \((rs/8)^N\). In the mixed case, the two possible sizes \(a'\in\{a-1,a\}\), when available, cover exactly the required interval of output sizes.

In Lemma 7.5, the reference diagonal is nonnegative even though this is not separately assumed: property (P) gives
\[
b_i=g(1,i;i)\ge0.
\]
Thus both reference and perturbed recurrence matrices have the norm properties used in the proof.

For Theorem 7.6, the chosen \(\eta\) is smaller than both \(p_0\) and the relevant upward-coefficient margins. The terminal coefficients remain exactly \(a_{2N}=0,c_{2N}=1\).

**Minor wording fix, Lemma 7.4:** replace “Every monomial coefficient … is … at least” by “Every nonzero term arising from a chosen reduction has coefficient at least …”.

### Quadratic decomposition and the \(N=1\) exception

Theorem 7.8 is correct. In particular, the odd support must omit \(t=0\), as the proof does. The normalized row sums are
\[
\frac{1-\hat b_0}{\hat a_0}=1,
\qquad
\frac{1-\check b_0}{\check a_0}=1,
\]
and the terminal upward coefficients vanish in both components.

**Defect: Corollary 7.9, component-identification sentence.**  
For \(N=1\), “parameters \((N-1,q,r/q)\)” means a length-zero array in a formula dividing by \([N-1]_q=0\).

**Replacement:**
> For \(N\ge2\), the normalized even and odd components have parameters \((N,q,r)\) and \((N-1,q,r/q)\), respectively. For \(N=1\), the odd component consists only of \(L_0=1\), and positivity follows directly from Theorem 7.1.

### Low products: the omitted calculation is valid

With \(\alpha_0=0\) and out-of-domain values of \(v\) set to zero, direct transposition gives
\[
(H^*v)(i,j)=
\alpha_i v(i-1,j)+\gamma_i v(i+1,j)
+(\beta_i-\beta_j)v(i,j)
-\alpha_jv(i,j-1)-\gamma_jv(i,j+1).
\]

For the stated checkerboard cone, this equals \(-\alpha_m\) at \((n,m)\). Elsewhere its nonzero values are precisely:

- \(\beta_i-\beta_j\) on the checkerboard interior;
- \(\alpha_i+\gamma_i-\alpha_j-\gamma_j\) on the other interior parity;
- \(\alpha_i-\alpha_j\) on \(i+j=n+m\);
- \(\gamma_i-\alpha_j\) on \(i-j=n-m\).

The paper’s respective index bounds are correct. In particular, no monotonicity assumption on \(b_N\) or on the terminal value \(\alpha_N+\gamma_N\) is needed.

**Concrete improvement:** insert this formula in Theorem 7.10 and explicitly set \(\alpha_0=0\). This makes the finite-boundary argument self-contained.

### Reversal normalization

**Defect: paragraph introducing Lemma 7.12.**  
Usually
\[
a'_0=c_N\ne1,\qquad b'_0=b_N\ne0.
\]
Thus the reversed system does not satisfy the paper’s initial normalization.

The identity remains correct with
\[
R'_0=1,\qquad R'_1(x)=\frac{x-b_N}{c_N}.
\]
The recurrence directly gives
\[
e_N^{\mathsf T}R'_t(J)=e_{N-t}^{\mathsf T},
\]
so the cyclicity proof works unchanged.

**Replacement:**
> The reversed array need not satisfy \(a'_0=1,b'_0=0\). Define its polynomials by the reversed recurrence, starting with \(R'_0=1\), so \(R'_1=(x-b_N)/c_N\). They still satisfy \(R'_t(1)=1\).

### An invalid application of Lemma 7.5

**Defect: paragraph after Corollary 7.9**, claiming positivity whenever the components satisfy Lemma 7.5 “around any reference with a margin”.

Lemma 7.5 only controls \(\Sigma\). Reference zeros outside \(\Sigma\) can become negative.

For example, start with \(K_{2,1}\) and change
\[
c_1=\tfrac12+\varepsilon,\qquad a_1=\tfrac12-\varepsilon,
\]
leaving \(b\equiv0,c_2=1\). Arbitrarily small perturbations satisfy Lemma 7.5 with \(\Sigma\) equal to the reference’s positive entries, but
\[
g(2,2;2)=\frac{-2\varepsilon}{1/2-\varepsilon}<0.
\]

**Replacement:**
> Lemma 7.5 supplies a positivity criterion when \(\Sigma\) contains every potentially nonzero perturbed coefficient, or when the remaining coefficients are separately known to remain nonnegative.

## B. Lemma 8.2: independent derivation confirms the identity

The statement is correct. The proof’s principal notation defect is that \(X_{ij}\) is used both for physical coordinates and eigenbasis coordinates. Write the latter as \(\widehat X_{ij}\).

### Generating function and eigenvectors

Directly from the subset model,
\[
R_n(\lambda_j)=\binom Nn^{-1}
\sum_h(-1)^h\binom jh\binom{N-j}{n-h}.
\]
Using
\[
\frac{\binom Nj}{\binom Nn}
\binom jh\binom{N-j}{n-h}
=
\binom nh\binom{N-n}{j-h},
\]
one obtains
\[
\sum_jw_jR_n(\lambda_j)s^j
=2^{-N}(1+s)^{N-n}(1-s)^n.
\]

Orthogonality gives
\[
\sum_n\pi_nR_n(\lambda_i)R_n(\lambda_j)
=\frac{\delta_{ij}}{w_j}.
\]
Therefore the stated \(u_j,v_j\), with
\(\pi_n=\binom Nn\) and \(w_j=2^{-N}\binom Nj\), are correctly biorthonormal.

### Commutator and elimination of diagonal terms

Differentiating the commuting relation gives
\[
[J,X]=[\Pi,E],\qquad e_0^{\mathsf T}X=0.
\]
Consequently,
\[
\widehat X_{ij}
=
\frac{((-1)^i-(-1)^j)\widehat E_{ij}}{\lambda_i-\lambda_j},
\quad i\ne j,
\qquad
\sum_i\widehat X_{ij}=0.
\]
Since \(\pi_N=1\), the physical corner derivative is
\[
h_N:=e_N^{\mathsf T}Xe_N
=\sum_{i,j}(-1)^{i+j}\widehat X_{ij}w_j.
\]
Eliminating \(\widehat X_{jj}\) yields exactly
\[
h_N
=N\sum_{i\ne j}\widehat E_{ij}w_j
\frac{(-1)^i-(-1)^j}{i-j}.
\]
There is no missing weight or sign here.

The integral identity is also correct:
\[
\frac{(-1)^i-(-1)^j}{i-j}
=-\pi\int_0^1\sin\!\bigl(\pi(\theta i+(1-\theta)j)\bigr)\,d\theta.
\]
At \(i=j\), both sides are interpreted as zero.

### Row contributions and beta integrals

Put \(C=\cos\phi,S=\sin\phi\). For an interior \(b_n\)-coordinate, direct substitution gives
\[
AB=-(-1)^n i^{N-1}C^NS^{N-1}e^{-i\phi},
\]
as printed.

For \(N=2h\),
\[
\int_0^{\pi/2}C^{N+1}S^{N-1}\,d\phi
=\frac{(h-1)!h!}{2(2h)!}
=\frac{|s_N|}{2N}.
\]
For \(N=2h+1\),
\[
\int_0^{\pi/2}C^NS^N\,d\phi
=\frac{(h!)^2}{2(2h+1)!}
=\frac{|s_N|}{2N}.
\]

For an interior \(c_n\)-coordinate, the ratio of the two \(B\)-expressions is \(e^{i\phi}/C\). After multiplication, the expression is nonsingular at the endpoints. It is real for odd \(N\), giving zero contribution. For even \(N\),
\[
\int C^{N-1}S^{N-1}=2\int C^{N+1}S^{N-1},
\]
giving twice the \(b_n\)-contribution.

For the terminal coordinate,
\[
AB=-(-i)^N C^{N-1}S^N e^{-i\phi},
\]
and the contribution is \(s_N\) for **both** parities.

Thus
\[
\partial_{b_n}g=s_N(-1)^n\binom Nn,\qquad
\partial_{c_n}g=
\begin{cases}
2s_N(-1)^n\binom Nn,&N\text{ even},\\
0,&N\text{ odd},
\end{cases}
\]
for \(n<N\), while \(\partial_{c_N}g=s_N\). These assemble into the stated formula only with the stipulated terminal convention \(\delta b_N=-\delta c_N\).

Exact differentiation gives, in the paper’s free-coordinate order,
\[
\begin{array}{c|l}
N&\nabla g(N,N;N)\\ \hline
2&(-2;\,-4,1)\\
3&(-3/2,3/2;\,0,0,1/2)\\
4&(4/3,-2,4/3;\,8/3,-4,8/3,-1/3).
\end{array}
\]

## C. Uniform rules and the analytic extension

### Definition 8.3 and Theorem 8.4

Specify the quantifiers as
\[
\exists N_0\ \forall N\ge N_0\ \exists\varepsilon_N>0\
\forall\,0<\varepsilon<\varepsilon_N.
\]
No common \(\varepsilon_N\) is needed.

For polynomial rules, the calculation
\[
\dot g_N=
\begin{cases}
-s_NL_{\rm even},&N\text{ even},\\
-s_NL_{\rm odd},&N\text{ odd}
\end{cases}
\]
is correct once \(N\) exceeds both degrees.

The sentence excluding an open set of polynomial rules is also correct **in the full coefficient space of polynomial pairs**. The two functionals are independent already on constant pairs:
\[
L_{\rm even}=2B+3C,\qquad L_{\rm odd}=-C.
\]
Hence the admitted polynomial rules lie in a codimension-two subspace, which has empty interior.

**Defect: examples immediately after Theorem 8.4.**  
“\(\gamma\) odd about \(1/2\)” is insufficient for the asserted palindromic example. Taking \(\gamma(x)=x-\tfrac12\), \(\beta=0\), gives
\[
L_{\rm even}=L_{\rm odd}=-\tfrac12.
\]
The endpoint conventions destroy palindromicity.

**Replacement:** require additionally \(\gamma(0)=\gamma(1)=0\). Also describe the geometric example as a tangent direction to the geometric family; the geometric theorem by itself concerns that family, not an arbitrary straight tangent ray.

### Lemma 8.5: completing the contour argument

Let \(D\) be the analytic domain and \(K_t=\{U\le-1+t\}\). The compactness argument correctly permits \(K_{3\eta}\subset D\).

Choose a bounded polygonal open set \(V\) with
\[
K_\eta\subset V,\qquad
\overline V\subset\{U<-1+3\eta\}.
\]
Its oriented boundary, possibly comprising several components, is the required cycle. It lies outside \(K_\eta\), winds once around every interpolation node, and bounds a region contained in \(D\).

Writing \(d=\operatorname{dist}(\Gamma,[0,1])>0\), one has uniformly
\[
\left|\frac{\partial}{\partial t}\log|x-t|\right|\le d^{-1}.
\]
Consequently,
\[
\sum_{k=0}^N\log|x-k/N|\ge NU(x)-C_\Gamma
\]
with \(C_\Gamma\) independent of \(N\). The residue prefactor and Stirling estimate then give the claimed
\(O(\sqrt N e^{-\eta N})\).

**Additional prose correction:** the description of \(\Omega\) as having “corners” at \(0,1\) is inaccurate in the usual angular sense. Near \(0\), its boundary satisfies
\[
\operatorname{Re}z\sim
\frac{\pi|\operatorname{Im}z|}
     {2\log(1/|\operatorname{Im}z|)},
\]
so it has a vertical tangent there. Replace “has corners” by “has nonanalytic boundary points”.

### Corollary 8.6 is false as a wholesale extension

The necessary equalities extend. Exact vanishing does not.

Take the entire functions
\[
\beta(x)=e^x-1-(e-1)x,\qquad \gamma(x)=0.
\]
Their endpoint values make both \(L\)’s zero, but for every \(N\ge2\),
\[
\dot g_N=s_N(1-e^{1/N})^N\ne0.
\]

**Replacement statement:**
> If \(\beta,\gamma\) are analytic on an open neighborhood of \(\Omega\), admission implies \(L_{\rm even}=L_{\rm odd}=0\). When these equalities hold, the corner derivative is \(O(|s_N|\sqrt N e^{-\eta N})\); it need not vanish exactly.

## D. Proposition 8.7

### Part (1): weak fixed sign does not imply eventual vanishing

From \(s_NA_N\ge0\), an eventually nonnegative even subsequence need only vanish where \(s_N<0\). It may remain positive on the other residue class.

This is not merely an abstract sequence objection: there are directions satisfying the proposition’s property-(P) assumption.

Define \(w_N\) by
\[
\delta b_n=0,\qquad
\delta c_n=-2\frac{N-n}{N}\binom{N-1}{n-1}
\quad(1\le n<N),\qquad
\delta c_N=0.
\]
These directions admit small positive straight rays with property (P). One verification starts from
\[
\mu_t=\mu_0-t(\delta_{-1}+\delta_1),
\]
where \(\mu_0\) is the symmetric Krawtchouk measure. Differentiation of orthogonality gives
\[
\dot R_j=
2\!\!\sum_{\substack{h<j\\h\equiv j\pmod2}}
\binom Nh(R_h-R_j),
\]
whose recurrence derivative is \(w_N\).

At each even perimeter zero, the linearization derivative is
\(4\binom Nk>0\). Parity zeros remain identically zero on the straight ray because \(b\equiv0\); the other coefficients are positive at the reference. Hence sufficiently small straight perturbations have (P). In particular, for even \(N\), \(\dot g(N,N;N)=4\).

Now use \(v_N=w_N\) for \(N\equiv2\pmod4\), and \(v_N=0\) otherwise. Then
\[
A_N=
\begin{cases}
4/s_N>0,&N\equiv2\pmod4,\\
0,&\text{otherwise}.
\end{cases}
\]
The even subsequence is nonnegative but not eventually zero.

If “constant sign” means that \(\operatorname{sgn}(A_N)\) is eventually literally constant, including zeros, part (1) is true—but that meaning must be explicit.

**Unambiguous replacement:**
> Along either parity class, \(A_N\) cannot be eventually strictly positive or eventually strictly negative. An eventual weak sign forces vanishing on the residue class where that sign conflicts with \(s_N\).

### Part (2): the conclusion is correct

Let \(D_Nf=\sum(-1)^n\binom Nn f(n/N)\). For sufficiently large \(N\), direct assembly gives
\[
A_N=
\begin{cases}
D_N(\beta+2\gamma)+P_e(N),&N\text{ even},\\
D_N\beta+P_o(N),&N\text{ odd},
\end{cases}
\]
where
\[
P_e(N)=q'_0-L_{\rm even}
+\sum_{k\ge1}(-1)^k\binom Nk
[p_k+q_k+2(p'_k+q'_k)],
\]
\[
P_o(N)=q'_0-L_{\rm odd}
+\sum_{k\ge1}(-1)^k\binom Nk(p_k-q_k).
\]

The sums are finite, so \(P_e,P_o\) are polynomials. A nonzero polynomial has a fixed strict sign eventually, and the exponentially small remainder cannot change that sign. Alternation of \(s_N\) therefore forces
\[
P_e\equiv P_o\equiv0.
\]
Independence of \(1,\binom N1,\binom N2,\ldots\) gives exactly the printed conditions.

**Required proof replacement:** use this direct polynomial argument, not part (1). Also say that the coefficients of the **combined polynomials \(P_e,P_o\)** vanish—not the coefficients of the layer polynomials before subtracting \(L\).

## E. Propositions 8.8 and Corollary 8.9

The smoothness assertion is valid. Polynomial coefficients and \(R_N(J)\) are rational functions of the recurrence entries, with denominators involving upward coefficients. Those coefficients are positive at \(K_{N,1}\). Thus \(G\) extends smoothly to an ordinary neighborhood of \((1,0)\), even outside the region \(b_i\ge0\).

A simpler complete proof of Proposition 8.8 avoids unspecified Taylor constants. Put \(d=|\dot g|>0\). On a sufficiently small rectangle,
\[
\partial_\varepsilon G(r,\varepsilon)\le-d/2.
\]
Therefore
\[
G(r,\varepsilon)\le(1-r)^N-\frac d2\varepsilon.
\]
Taking \(C=4/d\) proves the claim, after shrinking the rectangle to preserve the basic off-diagonal signs. The author’s uniform second-order bound is also legitimate on a compact subrectangle.

For Corollary 8.9, the following direction makes every admissibility issue explicit:
\[
\delta c_N=-\operatorname{sgn}(s_N),\qquad
\delta b_N=\operatorname{sgn}(s_N),
\]
with all other entries unchanged. Its corner derivative is \(-|s_N|\), and its full-array maximum norm is one.

Set \(t=1-r\) and \(\varepsilon=Ct^N\). For \(N\ge2\), eventually
\[
\varepsilon\le t/2,\qquad \varepsilon\le r/2.
\]
Hence
\[
\widetilde b_N\ge t/2,\qquad
\widetilde c_N\ge r/2,
\]
and every other coefficient remains admissible. The perturbation distance is exactly \(\varepsilon\), while its corner coefficient is negative.

Together with Theorem 5.3,
\[
\frac{1}{2(32N)^N}(1-r)^N
\le \rho_N(r)\le C_N(1-r)^N
\]
for \(r\) sufficiently close to one.

**Required correction to the original proof:** its free-coordinate \(\max|v|\) does not automatically control \(\delta a_i=-\delta b_i-\delta c_i\) with constant one. Use the full-array norm, allow a factor two, or use the terminal-only direction above.

The exclusion \(N=1\) is essential: every admissible two-point array with \(b_1\ge0\) already has (P), so the proposed finite radius-order assertion would fail there.

# 4. Claims stronger than what is proved

## The advertised general “disproof” is too broad

Theorem 8.4 excludes an open family of **bounded-degree, sampled polynomial affine directions**. Corollary 8.6, after correction, treats analytic directions on a specified complex neighborhood. Proposition 8.7 treats one particular bulk-plus-boundary-layer class.

These results do **not** exclude every uniform inequality criterion, every uniform rule, or nonlinear families of admissible arrays. Nor is “pure inequality criterion” formally defined.

**Replacement for the Section 8 opening and corresponding introduction/conclusion claims:**
> For uniformly sampled polynomial directions, and for the analytic and finite-boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary conditions. This does not exclude arbitrary uniform inequality criteria.

Without regularity, even the boundary functionals cannot be inferred from the sampled direction: changing \(\beta(0)\) changes neither \(v_N\) nor any array.

## “Inequalities alone” after Corollary 7.15 is false

The hypotheses explicitly contain
\[
b\equiv0,\qquad c_n+c_{N-n}=1.
\]
Those are equalities. The component version also requires exact component conditions.

**Replacement:**
> Within the symmetric palindromic subclass, monotonicity inequalities suffice.

## The final reversal paragraph in Section 7 is incorrect

The \(b_{N-1}<b_N\) argument violates condition (b) only when \(N\ge3\), because that condition requires \(1+1<N\).

Moreover, Szwarc’s array has \(b\equiv0\), so the displayed diagonal argument does not apply to it. Its reversal instead replaces \(p_0\) by \(1-p_0\), giving
\[
g'(2,2;2)=\frac{2p_0-1}{Np_0}<0.
\]
This obstructs condition (b) for length \(2N\) only when \(4<2N\), i.e. \(N\ge3\).

Replace the paragraph by these two separate, size-qualified statements. Delete the blanket assertion that their deep coefficients are positive “only through cancellation”.

The Miclo comparison also needs a small-size qualification: \(2^ia_i\) first increases from \(i=0\) to \(1\) for symmetric Krawtchouk precisely when \(N>2\). Sizes \(N=1,2\) do not violate that hypothesis.

## The fixed-\(N\) interior assertion needs proof, not finite evidence

The paragraph before Proposition 8.7 asserts the cone-interior claim for arbitrary fixed \(N\), then supplies computations only through \(N\le10\). Those computations do not prove the universal assertion. “Nothing can be excluded” is also too strong: nontrivial first-order inequalities certainly remain.

A mathematical repair is available. Decreasing the mass at \(x=1\) gives positive triple-integral derivative \(2\) at every perimeter zero. Adding a sufficiently large positive multiple of the Krawtchouk direction makes the derivatives positive at all remaining parity zeros inside the triangle. Thus a strict first-order direction exists for each fixed \(N\); continuity then gives an open cone of admissible rays. The manuscript should supply this argument or restrict its sentence to the computed sizes.

## The period-four computational claim is false as written

For the actual rule \(\beta\equiv1,\gamma\equiv0\) used in `rigidity_probe.py`, at \(r=4/5\) I obtain exactly
\[
\left.\partial_\varepsilon g(4,4;4)\right|_{\varepsilon=0}
=\frac{512}{1875}>0,
\]
but
\[
\left.\partial_\varepsilon g(8,8;8)\right|_{\varepsilon=0}
=-\frac{71936}{5859375}<0.
\]
These indices differ by four. Thus the unqualified period-four sign assertion away from \(r=1\) is incorrect. The companion script’s fixed-\(r\) routine tests finite perturbations, not the claimed derivative asymptotic. [1]

I did reproduce the stated fixed-size failures, all seven listed exact one-kink counterexamples through \(N=500\), and the three exact log-concave-increment examples. The two additional high-precision examples also reproduce at 80 and 150 digits. This supports those finite reports, not a general asymptotic theorem.

## Other computational overstatements

“Appear only at large \(N\), roughly \(5/r^2\)” is not established by displaying examples at selected sizes. No minimality or asymptotic scaling is proved.

The high-precision examples are not exact sign certificates without error bounds. The script itself distinguishes those floating-point calculations from its exact rational cases. [2]

Smooth convex profiles need not have log-concave increments. For example,
\[
d(x)=\frac{x+x^4}{2}
\]
is smooth and convex, but on the \(N=3\) grid its increments are
\[
14/81,\quad21/81,\quad46/81,
\]
which are not log-concave.

Finally, “only smooth deformations survived” and “finitely many local inequalities cannot enforce” smoothness are not consequences of the reported experiments. “Smooth” is not even defined for the relevant uniform family. Replace these sentences by a narrowly specified report of the tested families and ranges, and weaken the corresponding claims in Section 9.

**Additional normalization correction:** “An affine change of \(x\) reduces every finite system to this form” should include positive degree-wise normalization at the largest support point; an affine variable change alone does not generally impose all row sums.

**Attribution limitation:** the linked Szwarc survey PDF was not retrievable during this review. The low-product calculation above was reconstructed independently, so that limitation does not affect its mathematical verification; I do not certify the survey’s exact historical transcription.

Sources:
[1] https://raw.githubusercontent.com/skypher/szkraw/693b1e942e093f013c304701d590f26e8a637cb1/rigidity_probe.py
[2] https://raw.githubusercontent.com/skypher/szkraw/693b1e942e093f013c304701d590f26e8a637cb1/smallr_probe.py



## Corrected paper source (paper.tex)

```latex
\documentclass[twoside,10pt]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath,amssymb,amsthm,amsfonts,mathtools}
\usepackage[letterpaper,total={5.5in,8in},vmarginratio=1:1,hmarginratio=1:1,headsep=21pt]{geometry}
\usepackage{xcolor}
\usepackage[breaklinks=true,linktocpage=true]{hyperref}
\hypersetup{colorlinks=true,linkcolor=purple,urlcolor=purple,citecolor=blue!80!black,
pdfauthor={Leslie P. Polzer},pdftitle={Coefficient criteria for finite nonnegative linearization},
pdfsubject={Recurrence conditions, quadratic systems and quantitative stability for finite orthogonal polynomials},
pdfkeywords={orthogonal polynomials, Krawtchouk polynomials, nonnegative linearization, quadratic transformation, hypergroups, Lean}}
\medmuskip=4mu
\thickmuskip=8mu
\setlength{\emergencystretch}{2em}
\numberwithin{equation}{section}
\newtheoremstyle{slbody}{8pt}{8pt}{\normalfont\slshape}{}{\bfseries}{.}{0.5em}
{\thmname{#1}\thmnumber{ #2}\thmnote{ {\normalfont\itshape(\ignorespaces#3\unskip)}}}
\theoremstyle{slbody}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\renewcommand{\qedsymbol}{$\blacksquare$}
\newcommand{\qint}[1]{[#1]_q}
\title{Coefficient criteria for finite nonnegative linearization}
\author{Leslie P. Polzer}
\newcommand{\authoraffiliation}{Independent Researcher}
\newcommand{\authoremail}{polzer@fastmail.com}
\date{October 19, 2026}
\makeatletter
\renewcommand{\section}{\@startsection{section}{1}{\z@}{-3.5ex \@plus -1ex \@minus -.2ex}{2.3ex \@plus .2ex}{\normalfont\large\bfseries}}
\renewcommand{\@seccntformat}[1]{\csname the#1\endcsname.\enspace}
\def\tagform@#1{\maketag@@@{(\ignorespaces{\oldstylenums{#1}}\unskip\@@italiccorr)}}
\renewcommand{\eqref}[1]{\textup{{\normalfont(\oldstylenums{\ref{#1}}}\normalfont)}}
\newcommand{\shorttitle}{FINITE NONNEGATIVE LINEARIZATION}
\newcommand{\shortauthors}{LESLIE P. POLZER}
\newcommand{\ps@bookheader}{%
\renewcommand\@oddfoot{\hfil}\renewcommand\@evenfoot{\hfil}%
\renewcommand\@oddhead{\ifnum\value{page}>1{\small\hfil\shortauthors}\hfil\thepage\else\hfil\fi}%
\renewcommand\@evenhead{\thepage\hfil\small\shorttitle\hfil}}
\pagestyle{bookheader}
\renewcommand{\maketitle}{\begin{center}{\large\bfseries\@title}\\\vskip36pt
{\scshape\@author}\par\medskip{\small\authoraffiliation}\par\smallskip
{\small\texttt{\authoremail}}\par\smallskip{\small\@date}\par\vskip36pt\end{center}}
\makeatother
\renewenvironment{abstract}{\quotation\noindent\small{\bfseries\abstractname.\enspace}}{\endquotation}
\begin{document}
\maketitle

\begin{abstract}
We give two sufficient criteria stated directly in the coefficients of a finite stochastic three-term recurrence. The first assumes that the sum of its diagonal and downward coefficients has positive geometric increments with ratio $q\geq1$, and that the ratio of those coefficients is constant and nonnegative. A finite algebra construction gives nonnegative linearization, including products beyond the terminating degree. This includes the full positive Krawtchouk range and the dual $q$-Krawtchouk family with nonconstant increments. The underlying quadratic algebra occurs in Koelink's work on type B Hecke algebras. The second criterion gives explicit perturbation inequalities admitting a relatively open neighborhood of recurrence arrays around every Krawtchouk system in the interior of the positive linearization range. For symmetric finite systems, a quadratic decomposition reduces positivity to two nonsymmetric finite systems. This yields a parity-split criterion covering Szwarc's quadratic system for $p_0\leq1/2$ and a $q$-analogue, and explicit symmetric neighborhoods. None of the criteria requires computing general linearization coefficients.
\vskip5pt
\noindent\textbf{Keywords.}\enspace Finite orthogonal polynomials; nonnegative linearization; Krawtchouk polynomials; dual $q$-Krawtchouk polynomials; quadratic transformation; polynomial hypergroups.
\vskip5pt
\noindent\textbf{MSC2020 Classification.}\enspace 33C45; 33D45; 42C05.
\end{abstract}

\vskip50pt
\baselineskip=13.5pt
\section{Introduction}\label{sec:introduction}

Nonnegative linearization (property (P)) asks whether the product of two orthogonal polynomials is a nonnegative linear combination of polynomials in the same basis. For a finite system, the identity is understood on the orthogonality support. This distinction is essential when the formal product degree exceeds the terminal degree. In a normalization with $R_i(1)=1$, nonnegative coefficients have sum one and define the product probabilities of a finite polynomial hypergroup.

The Krawtchouk case is classical. Eagleson~\cite{eagleson} studied positive definite sequences for these polynomials in 1969; Szwarc~\cite[\S5, Problem~2]{szwarc} records the nonnegative-linearization range as $0<p_0\leq1/2$ for binomial weights $\binom Njp_0^{N-j}(1-p_0)^j$ when normalized at $j=0$.\footnote{The linked author version, \S5, Problem~2, printed p.~125, uses inconsistent parameter conventions: its displayed weights have mean $N(1-p)$, whereas its degree-zero recurrence gives $K_1(x)=(x-pN)/((1-p)N)$. Thus the displayed weights give $\int K_1\,d\mu=(1-2p)/(1-p)$. Corollary~\ref{cor:kraw} derives our weights and normalization directly.} Our proof below fixes that convention directly from a two-point model. It does not treat Krawtchouk positivity itself as a new result.

Recurrence methods also have a long history. In the second note of his 1969 report, Askey~\cite[Part~II, Theorem~1 and Corollary~1]{askey} gives finite recurrence conditions leading to a hyperbolic difference-equation maximum principle. The stated polynomial conclusion concerns products with degree sum at most $N$. Szwarc's later characterization~\cite[Theorem~1]{szwarc2003} treats finite as well as infinite systems through an auxiliary discrete hyperbolic problem. His 2005 survey nevertheless asks for criteria for finite systems, including Krawtchouk and its quadratic system $Q_n$ (Section~\ref{sec:szwarc})~\cite[\S5, Problem~2]{szwarc}. Here we seek structural assumptions on the recurrence coefficients that imply positivity for every finite product.

Koelink~\cite[Theorems~3.1(ii) and 7.8]{koelink} constructed a triangular quadratic algebra associated with the type B Hecke algebra, and identified the corresponding $q$-Krawtchouk spherical functions. The dual recurrence in that construction is the geometric family used below. Our algebraic proof extracts its positive multiplication mechanism and expresses the resulting sufficient condition as two scalar patterns in a stochastic recurrence: a constant ratio and geometric increments. No priority is claimed for the algebra or for the resulting named family. For comparison, Miclo~\cite[Proposition~3.3]{miclo} gives a spectral characterization of the hypergroup property at a boundary point for irreducible finite birth--death chains by entrywise nonnegativity of products of transition matrices shifted by eigenvalues of their leading principal submatrices.

The second criterion is quantitative stability. Around each Krawtchouk array in the interior of the positive linearization range ($0<r<1$, equivalently $0<p_0<1/2$), we exhibit an explicit radius in the space of recurrence coefficients within which all finite products remain nonnegative. Its proof uses one positive term to obtain a reference margin, an error recurrence to control perturbations, and orthogonality to preserve exact zeros outside the triangle support. The resulting neighborhoods contain independently varying coefficient arrays, rather than only a reparametrized classical family. The radius is deliberately conservative and depends on $N$; no uniform stability radius at the symmetric endpoint is asserted.

Section~\ref{sec:criterion} states the geometric criterion. Sections~\ref{sec:algebra} and~\ref{sec:normalization} give its algebraic proof. Section~\ref{sec:perturbation} proves the perturbation inequalities, including explicit nongeometric examples. Section~\ref{sec:applications} fixes the Krawtchouk normalization and compares the geometric recurrence with Koelink's construction. Section~\ref{sec:szwarc} treats Szwarc's quadratic system and inequality hypotheses away from the deepest products. Section~\ref{sec:limits} proves that uniformly sampled polynomial or analytic deformations of the symmetric Krawtchouk systems that keep property (P) must satisfy two first-order equalities, shows that the stability radius of Theorem~\ref{thm:perturbation} has the optimal order in $1-r$, and records counterexamples to inequality shape conditions at smaller $r$. The final section lists questions left by these results.

\section{Statement and conventions}\label{sec:criterion}
For integers $j\geq0$ put $[j]_q=1+q+\cdots+q^{j-1}$, with $[0]_q=0$; in particular $[j]_1=j$.
Consider real coefficients indexed by $0\leq i\leq N$, where $N\geq1$, satisfying
\begin{equation}\label{eq:basic}
\begin{gathered}
a_0=1,\quad b_0=c_0=0,\quad a_N=0,\quad a_i+b_i+c_i=1,\\
a_i>0\ (i<N),\qquad c_i>0\ (i>0).
\end{gathered}
\end{equation}
Set $R_{-1}=0$, $R_0=1$, and determine $R_1,\ldots,R_N$ by
\begin{equation}\label{eq:recurrence}
xR_i=a_iR_{i+1}+b_iR_i+c_iR_{i-1}\qquad(0\leq i<N).
\end{equation}
At $i=0$, \eqref{eq:recurrence} gives $R_1=x$; induction at $x=1$, using the row sums and $a_i>0$ for $i<N$, gives $R_i(1)=1$ for $0\leq i\leq N$.
The terminal relation is $(x-b_N)R_N-c_NR_{N-1}=0$ on the orthogonality support. Linearization means equality of functions on this support, rather than an unrestricted polynomial identity when the degree sum exceeds $N$.

\begin{samepage}
\begin{theorem}[Geometric increment criterion]\label{thm:criterion}
Assume \eqref{eq:basic}. Set $d_i=b_i+c_i$. Suppose
\begin{enumerate}
\item $b_i/c_i=\beta$ for every $1\leq i\leq N$, where $\beta\geq0$;
\item $\delta_i=d_i-d_{i-1}>0$ for $1\leq i\leq N$;
\item for some $q\geq1$, $\delta_{i+1}=q\delta_i$ whenever $1\leq i<N$.
\end{enumerate}
Then the recurrence has a positive orthogonality measure on exactly $N+1$ distinct real points. Its normalized polynomials satisfy
\begin{equation}\label{eq:positive}
R_mR_n=\sum_{k=0}^N g(m,n;k)R_k,
\qquad g(m,n;k)\geq0,\qquad\sum_{k=0}^N g(m,n;k)=1
\end{equation}
on that support for all $0\leq m,n\leq N$.
\end{theorem}
\end{samepage}

\begin{lemma}[Coefficient parametrization]\label{lem:parameters}
The hypotheses of Theorem~\ref{thm:criterion} are equivalent to
\begin{equation}\label{eq:parameters}
a_i=\frac{q^i[N-i]_q}{[N]_q},\qquad
b_i=(1-r)\frac{[i]_q}{[N]_q},\qquad
c_i=r\frac{[i]_q}{[N]_q}
\end{equation}
for $q\geq1$, $0<r\leq1$. When $N=1$, one may choose $q=1$.
\end{lemma}
\begin{proof}
The terminal sum gives $d_N=1$, and $d_0=0$. Geometric increments give $d_i=\delta_1[i]_q$, hence $\delta_1=1/[N]_q$. The constant ratio gives $c_i=d_i/(1+\beta)$ and $b_i=\beta d_i/(1+\beta)$. Put $r=(1+\beta)^{-1}$. Finally $[N]_q-[i]_q=q^i[N-i]_q$. These calculations reverse to give the converse, including $q=1$ and $N=1$.
\end{proof}

The parameter conventions used below are
\[
\begin{array}{c|l}
q & q\geq1\quad\text{(geometric increment ratio)}\\
\beta & b_i/c_i\geq0\\
r & 1/(1+\beta)\in(0,1]\\
p & 1/r=1+\beta\geq1\\
p_0 & r/(1+r)\in(0,1/2]\\
\text{symmetric Krawtchouk case} & r=1,\quad p_0=1/2
\end{array}
\]

\section{A finite algebra with positive multiplication}\label{sec:algebra}
Fix $p\geq1$ and $q\geq1$. Starting with $A_{N+1}=\mathbb R$, form recursively the commutative real algebras
\begin{equation}\label{eq:algebra}
A_j=A_{j+1}[z_j]\big/
\left(z_j^2-\left((q-1)\sum_{l=j+1}^N z_l+p-1\right)z_j-pq^{N-j}\right).
\end{equation}
Write $A=A_1$. For $S\subseteq\{1,\ldots,N\}$ let $z_S=\prod_{j\in S}z_j$, with $z_\varnothing=1$.

\begin{lemma}[Basis and positivity]\label{lem:basis}
The elements $z_S$ form a basis of $A$, and all their multiplication coefficients are nonnegative.
\end{lemma}
\begin{proof}
Division by a monic quadratic over any commutative coefficient ring gives a unique remainder of degree at most one. Applying this successively in \eqref{eq:algebra} gives the asserted basis and dimension $2^N$.
For positivity, replace a square by
\[
z_j^2=(q-1)\sum_{l>j}z_jz_l+(p-1)z_j+pq^{N-j}.
\]
Every displayed coefficient is nonnegative. This rewriting terminates: give $z_j$ weight $2^{N-j}$ and give a monomial the sum of the weights of its factors, counted with multiplicity. Each replacement strictly decreases this nonnegative integer weight, because $l>j$ implies $2^{N-l}<2^{N-j}$. The final expression is in the unique squarefree basis, proving the claim.
\end{proof}

\begin{lemma}[Positive associative inner product]\label{lem:trace}
Let $\tau$ extract the coefficient of $z_\varnothing$. Then
\begin{equation}\label{eq:trace}
\tau(z_Sz_T)=\boldsymbol1_{S=T}\,p^{|S|}q^{\sum_{j\in S}(N-j)}.
\end{equation}
Consequently $\langle u,v\rangle=\tau(uv)$ is positive definite, and multiplication by every element of $A$ is self-adjoint.
\end{lemma}
\begin{proof}
Induct downwards through the tower. If $j$ belongs to exactly one of $S,T$, their product has the form $z_jv$ with $v\in A_{j+1}$ and has zero constant coefficient in $z_j$. If it belongs to both, the constant coefficient in $z_j$ is $pq^{N-j}z_{S\setminus\{j\}}z_{T\setminus\{j\}}$ by \eqref{eq:algebra}. If it belongs to neither, pass to $A_{j+1}$. Iteration proves \eqref{eq:trace}. All diagonal factors are positive. Associativity and commutativity give $\tau((hu)v)=\tau(u(hv))$.
\end{proof}

Put $E_k=\sum_{|S|=k}z_S$ for $0\leq k\leq N$, and set $E_{-1}=E_{N+1}=0$.

\begin{lemma}[Three-term multiplication]\label{lem:three}
For $0\leq k\leq N$,
\begin{equation}\label{eq:three}
E_1E_k=[k+1]_qE_{k+1}+(p-1)[k]_qE_k+
pq^{k-1}[N-k+1]_qE_{k-1}.
\end{equation}
The last term is interpreted as zero for $k=0$.
\end{lemma}
\begin{proof}
For $k=0$ the identity reads $E_1=E_1$. For $N=1,k=1$ it is exactly $z_1^2=(p-1)z_1+p$.
For the induction on $N$, write $F_j$ for the elementary squarefree sums in $z_2,\ldots,z_N$, with $F_j=0$ outside $0\leq j\leq N-1$. Then $E_k=F_k+z_1F_{k-1}$ and $E_1=F_1+z_1$. For $1\leq k\leq N-1$, use \eqref{eq:algebra} to obtain
\[
E_1E_k=F_1F_k+z_1F_k+qz_1F_1F_{k-1}
 +(p-1)z_1F_{k-1}+pq^{N-1}F_{k-1}.
\]
Apply the induction hypothesis to $F_1F_k$ and $F_1F_{k-1}$. The coefficients of $F_{k+1}$ and $z_1F_k$ are respectively $[k+1]_q$ and $1+q[k]_q=[k+1]_q$. The coefficients of $F_k$ and $z_1F_{k-1}$ are both $(p-1)[k]_q$, since $1+q[k-1]_q=[k]_q$. The coefficient of $F_{k-1}$ is
\[
pq^{k-1}[N-k]_q+pq^{N-1}=pq^{k-1}[N-k+1]_q,
\]
which is also the coefficient of $z_1F_{k-2}$. Regrouping gives \eqref{eq:three}.
For the endpoint $k=N$, $E_N=z_1F_{N-1}$, so the same square relation gives
\[
E_1E_N=qz_1F_1F_{N-1}+(p-1)z_1F_{N-1}+pq^{N-1}F_{N-1}.
\]
The tail endpoint identity is
\[
F_1F_{N-1}=(p-1)[N-1]_qF_{N-1}+pq^{N-2}F_{N-2}.
\]
Substitution gives $(p-1)[N]_qE_N+pq^{N-1}E_{N-1}$, as required. This separately checks the terminating boundary.
\end{proof}

\begin{proposition}[Positive subalgebra]\label{prop:subalgebra}
The space $B=\operatorname{span}\{E_0,\ldots,E_N\}$ is the subalgebra generated by $E_1$. Every product $E_mE_n$ has nonnegative coefficients in this basis.
\end{proposition}
\begin{proof}
All $E_k$ are independent, since their squarefree supports are nonempty and disjoint. Equation~\eqref{eq:three} shows that $B$ is invariant under multiplication by $E_1$. Since $[k+1]_q>0$, its interior recurrence also expresses each $E_{k+1}$ as a polynomial in $E_1$. Thus $B=\mathbb R[E_1]$, proving closure under multiplication, including products of total index greater than $N$.
Expand such a product as $\sum_k h_kE_k$. Its coefficient at each squarefree monomial $z_S$ is $h_{|S|}$. Lemma~\ref{lem:basis} makes that coefficient nonnegative. There is a subset of each cardinality $0,\ldots,N$, so every $h_k$ is nonnegative.
\end{proof}

\section{Normalization and the finite orthogonal system}\label{sec:normalization}
\begin{lemma}[Positive normalization]\label{lem:normalization}
Evaluation $z_j\mapsto pq^{N-j}$ defines an algebra character $\epsilon$ of $A$. Put $t_k=\epsilon(E_k)>0$. Then
\begin{equation}\label{eq:ratio}
t_0=1,\quad t_1=p[N]_q,\qquad
\frac{t_{k+1}}{t_k}=pq^k\frac{[N-k]_q}{[k+1]_q}\quad(0\leq k<N).
\end{equation}
\end{lemma}
\begin{proof}
For $h=N-j$, substitution in the right-hand side of \eqref{eq:algebra} gives
\[
(q-1)p^2q^h[h]_q+(p-1)pq^h+pq^h
=p^2q^h\big((q-1)[h]_q+1\big)=p^2q^{2h}.
\]
Thus all defining relations hold. The generating polynomial of the $t_k$ is
$T(u)=\prod_{j=0}^{N-1}(1+pq^ju)$, whose coefficients are strictly positive.
When $q>1$, the identity $(1+pu)T(qu)=(1+pq^Nu)T(u)$ gives
$(q^k-1)t_k=p(q^N-q^{k-1})t_{k-1}$ for $1\leq k\leq N$, which is \eqref{eq:ratio}. When $q=1$, $t_k=\binom Nk p^k$ and the same ratio follows directly.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:criterion}]
Use Lemma~\ref{lem:parameters} and put $p=1/r\geq1$. Construct $A,B$ as above and set $X=E_1/t_1$, $U_k=E_k/t_k$. Divide \eqref{eq:three} by $t_1t_k$ and use \eqref{eq:ratio}. The three coefficients are
\begin{align*}
\frac{[k+1]_qt_{k+1}}{p[N]_qt_k}
&=\frac{q^k[N-k]_q}{[N]_q},\\
\frac{(p-1)[k]_q}{p[N]_q}&=(1-r)\frac{[k]_q}{[N]_q},\\
\frac{pq^{k-1}[N-k+1]_qt_{k-1}}{p[N]_qt_k}
&=r\frac{[k]_q}{[N]_q}.
\end{align*}
At $k=0$ omit the third expression; at $k=N$ omit the first. Consequently $U_k=R_k(X)$ for every $k\leq N$, with the stated terminal relation.

The orthogonality support follows from the real spectral theorem in finite dimensions. On $B$ use the positive inner product from Lemma~\ref{lem:trace}. Multiplication by $X$ is self-adjoint. The vector $1=E_0$ is cyclic because the $E_k$ are polynomials of successive degrees in $X$ and form a basis. In an orthogonal eigenspace decomposition of a self-adjoint operator, the cyclic span of one vector has dimension at most the number of distinct eigenvalues. Here the cyclic span has dimension $N+1$, so there are exactly $N+1$ distinct eigenvalues, and the projection of $1$ on every eigenspace is nonzero. Give each eigenvalue the squared norm of that projection as its mass. All masses are positive, sum to $\langle1,1\rangle=1$, and yield
\[
\int f(x)h(x)\,d\mu(x)=\langle f(X),h(X)\rangle
\]
for real polynomials $f,h$, identifying an algebra element with its action on $1$. The $E_k$ are orthogonal by \eqref{eq:trace}, so the $R_k$ are orthogonal for this measure.

Proposition~\ref{prop:subalgebra} and positive $t_k$ give nonnegative product coefficients for the $U_k$. Applying the character $\epsilon$ gives their sum equal to one because $\epsilon(U_k)=1$. Polynomial identities in the algebra hold on every spectral point; conversely the $R_k$, having successive degrees at most $N$, form a basis of functions on the $N+1$ distinct points. This proves uniqueness and \eqref{eq:positive} for all products.
\end{proof}

\section{A criterion for small coefficient perturbations}\label{sec:perturbation}

Write the tridiagonal recurrence matrix with the row convention
\[
J_{i,i+1}=a_i,\qquad J_{i,i}=b_i,\qquad J_{i,i-1}=c_i,
\]
with all other entries zero and indices outside $0,\ldots,N$ omitted.

\begin{lemma}[Finite recurrence realization and triangle support]\label{lem:finite}
Every recurrence satisfying \eqref{eq:basic} has a positive orthogonality measure on exactly $N+1$ real points. If $J$ is its tridiagonal recurrence matrix, then its finite product coefficients satisfy
\begin{equation}\label{eq:matrix-product}
g(m,n;k)=[R_m(J)]_{n,k}.
\end{equation}
They vanish unless $|m-n|\leq k\leq\min(m+n,N)$, regardless of their signs inside this interval.
\end{lemma}
\begin{proof}
Choose positive $\pi_i$ with $\pi_0=1$ and $\pi_{i+1}=\pi_i a_i/c_{i+1}$. For $D=\operatorname{diag}(\sqrt{\pi_i})$, $H=DJD^{-1}$ is real symmetric. Induction in \eqref{eq:recurrence} gives the row-vector identity $e_0^\mathsf T R_i(J)=e_i^\mathsf T$, hence $e_0^\mathsf T R_i(H)=\pi_i^{-1/2}e_i^\mathsf T$. In particular $e_0$ is cyclic for $H$. The same finite spectral argument as in Theorem~\ref{thm:criterion} gives $N+1$ distinct eigenvalues and positive spectral masses at $e_0$, and
\[
\int R_iR_j\,d\mu=e_0^\mathsf TR_i(H)R_j(H)e_0
=\boldsymbol1_{i=j}\pi_i^{-1}.
\]
The terminal relation holds on this support: its polynomial $Q(x)=(x-b_N)R_N-c_NR_{N-1}$ satisfies $e_0^\mathsf TQ(J)=0$. Since $e_0$ is cyclic and $Q(J)$ commutes with $J$, $Q(J)=0$.
Multiplying a basis polynomial by $x$ acts by the corresponding row of $J$, including the terminal row. Induction on powers of $x$ therefore gives \eqref{eq:matrix-product}. Orthogonality also gives
\[
g(m,n;k)=\frac{\int R_mR_nR_k\,d\mu}{\int R_k^2\,d\mu}.
\]
If one of $m,n,k$ exceeds the sum of the other two, its polynomial is orthogonal to their product, whose degree is smaller. This proves the asserted support.
\end{proof}

\begin{lemma}[A uniform positive margin in the asymmetric case]\label{lem:margin}
For the Krawtchouk recurrence \eqref{eq:parameters} with $q=1$ and $0<r<1$, put $s=\min(r,1-r)$. Every coefficient in its triangle support obeys
\begin{equation}\label{eq:margin}
g(m,n;k)\geq (s/4)^N\quad\text{if }|m-n|\leq k\leq\min(m+n,N).
\end{equation}
\end{lemma}
\begin{proof}
Specialize the algebra above to $q=1$, and put $y_i=z_i/p$, where $p=1/r$. Then $y_i^2=(1-r)y_i+r$, and $U_m=\binom Nm^{-1}\sum_{|S|=m}y_S$. The reduction of a product $y_Sy_T$ has nonnegative coefficients, each chosen term being a product of at most $N$ factors from $\{r,1-r\}$. Its coefficient is therefore at least $s^N$.
For each admissible $k$, at least one such term has degree $k$. Assume $m\geq n$. If $k\leq m$, take $T\subseteq S$, with sizes $n,m$, and retain the linear term for exactly $k-(m-n)$ overlap coordinates. This number lies between $0$ and $n$. If $k\geq m$, choose sets with overlap $m+n-k$ and union of size $k\leq N$, and retain the linear term at every overlap coordinate.
Permutation symmetry makes the coefficient of $y_U$ depend only on $|U|=k$. Hence the coefficient in the normalized elementary-symmetric basis is at least
\[
\frac{s^N\binom Nk}{\binom Nm\binom Nn}\geq\frac{s^N}{4^N}.
\]
This uses a single positive term and a denominator bound, not an explicit formula for the product coefficients.
\end{proof}

\begin{theorem}[Explicit perturbation inequalities]\label{thm:perturbation}
Let $N\geq1$, $0<r<1$, $s=\min(r,1-r)$, and
\begin{equation}\label{eq:radius}
\eta_N(r)=\frac12\left(\frac{s}{32N}\right)^N.
\end{equation}
Suppose coefficients $\widetilde a_i,\widetilde b_i,\widetilde c_i$ satisfy \eqref{eq:basic}, with $\widetilde b_i\geq0$ for every $i$, and
\begin{equation}\label{eq:closeness}
\max_{0\leq i\leq N}\left\{
\left|\widetilde a_i-\frac{N-i}{N}\right|,
\left|\widetilde b_i-\frac{(1-r)i}{N}\right|,
\left|\widetilde c_i-\frac{ri}{N}\right|\right\}\leq\eta_N(r).
\end{equation}
Then the finite system has nonnegative linearization. Throughout its triangle support,
\[
\widetilde g(m,n;k)\geq\tfrac12(s/4)^N.
\]
The product coefficients sum to one.
\end{theorem}
\begin{proof}
Use tildes for the perturbed system and untilded letters for its $q=1$ reference at $r$. Let $\eta=\eta_N(r)$ and use the maximum absolute row-sum matrix norm. Both $J$ and $\widetilde J$ are stochastic matrices, so $\|J\|_\infty=\|\widetilde J\|_\infty=1$ and $\|\widetilde J-J\|_\infty\leq3\eta$. Put $B_m=R_m(J)$, $\widetilde B_m=\widetilde R_m(\widetilde J)$ and $e_m=\|\widetilde B_m-B_m\|_\infty$. Theorem~\ref{thm:criterion} at $q=1$ and \eqref{eq:matrix-product} give $\|B_m\|_\infty=1$ for all $m\leq N$. Also $e_0=0$ and $e_1\leq3\eta$.

Subtract the two matrix recurrences for $1\leq m<N$. Writing $\Delta_m=\widetilde B_m-B_m$ gives exactly
\begin{align*}
\widetilde a_m\Delta_{m+1}
={}&(\widetilde J-\widetilde b_m I)\Delta_m-\widetilde c_m\Delta_{m-1}\\
 &+\big(\widetilde J-J-(\widetilde b_m-b_m)I\big)B_m\\
 &-(\widetilde c_m-c_m)B_{m-1}-(\widetilde a_m-a_m)B_{m+1}.
\end{align*}
Since $\eta\leq1/(2N)$, $\widetilde a_m\geq1/(2N)$. The terms not containing a $\Delta$ have combined norm at most $6\eta$. Also $0\leq\widetilde b_m,\widetilde c_m\leq1$, so
\begin{equation}\label{eq:error-recursion}
e_{m+1}\leq4Ne_m+2Ne_{m-1}+12N\eta.
\end{equation}
Set $L=8N$. Induction gives $e_m\leq\eta L^m$ for $1\leq m\leq N$: the base case follows from $3\leq L$, and, for $m\geq1$,
\[
4N+\frac{2N}{L}+\frac{12N}{L^m}
\leq4N+\frac14+\frac32\leq8N=L.
\]
Thus every matrix entry differs from its reference by at most
\[
\eta(8N)^N=\frac12(s/4)^N.
\]
Lemma~\ref{lem:margin} gives the positive lower bound on triangle entries, while Lemma~\ref{lem:finite} makes all entries outside the triangle exactly zero. Finally $\widetilde R_m(1)=1$ follows by recurrence from the stochastic coefficient sums, so evaluating each product at $1$ gives coefficient sum one. Here $1$ belongs to the support because $\widetilde J\boldsymbol1=\boldsymbol1$ and Lemma~\ref{lem:finite} identifies that support with its spectrum. No product-positivity inequality for the perturbed system has been assumed.
\end{proof}

\begin{corollary}[Finite systems outside the geometric family]\label{cor:nonclassical}
For every $N\geq2$, take the Krawtchouk coefficients at $r=1/2$, and replace only
\[
a_1\longmapsto a_1-h,\qquad b_1\longmapsto b_1+h,
\qquad 0<h\leq\frac14(64N)^{-N}.
\]
These recurrences have nonnegative linearization and do not satisfy the constant-ratio hypothesis of Theorem~\ref{thm:criterion}. More generally, Theorem~\ref{thm:perturbation} admits a relatively open neighborhood of the asymmetric Krawtchouk array in the affine space defined by the row-sum and boundary equalities in \eqref{eq:basic}.
\end{corollary}
\begin{proof}
All initial and terminal conventions and stochastic sums are preserved. The bound on $h$ is half the radius \eqref{eq:radius} at $r=1/2$, and is smaller than $a_1=(N-1)/N$, so all required signs hold. The perturbation theorem applies. At index $1$, $b_1/c_1=1+2Nh>1$, whereas at index $N$ the ratio remains $1$; these indices differ because $N\geq2$. Thus this array lies outside the geometric family. At the asymmetric reference, all free coefficients constrained to be positive are strictly positive; the strict version of \eqref{eq:closeness} therefore contains a relatively open neighborhood in that affine space; the sign conditions define the admissible region within it.
\end{proof}

\section{Applications and scope}\label{sec:applications}
\begin{corollary}[Full positive Krawtchouk range]\label{cor:kraw}
For every $N\geq1$ and $0<p_0\leq1/2$, Krawtchouk polynomials orthogonal for binomial weights $\binom Nj p_0^{N-j}(1-p_0)^j$ have nonnegative linearization when normalized at $j=0$.
\end{corollary}
\begin{proof}
To fix the convention without relying on a named recurrence, put $r=p_0/(1-p_0)\in(0,1]$, and let $Y_1,\ldots,Y_N$ be independent variables with values $1,-r$ of probabilities $p_0,1-p_0$. Their mean is zero and $Y_i^2=(1-r)Y_i+r$. The normalized elementary symmetric sums
\[
K_i(j)=\binom Ni^{-1}\sum_{|S|=i}\prod_{l\in S}Y_l
\]
depend only on the number $j$ of negative coordinates. They are orthogonal, because the expectation of two distinct squarefree monomials is zero: some independent mean-zero variable occurs once. Their weights in $j$ are exactly the stated binomial weights. With $x=N^{-1}\sum_lY_l=1-j/(N(1-p_0))$, multiplication by $x$ gives
\[
xK_i=\frac{N-i}{N}K_{i+1}+(1-r)\frac iN K_i+r\frac iN K_{i-1}.
\]
Indeed, in multiplying the elementary sum by $\sum_lY_l$, indices outside a subset give $(i+1)$ copies of each subset of size $i+1$; the linear part of $Y_l^2$ gives $(1-r)i$ copies of each subset of size $i$; and the constant part gives $r(N-i+1)$ copies of each subset of size $i-1$. Division by the binomial normalizers gives the displayed recurrence, including $i=N$. Its leading coefficient in $x$ is positive, its degree is $i$, and its value at $j=0$ is one. These properties identify the normalized orthogonal polynomials for the binomial measure. Apply Theorem~\ref{thm:criterion} with $q=1$.
The range is sharp in this endpoint normalization: if $1/2<p_0<1$, then
$r=p_0/(1-p_0)>1$ and $g(1,1;1)=b_1=(1-r)/N<0$.
For $N=1$, this coefficient follows from the terminal relation.
\end{proof}

\begin{corollary}[The dual $q$-Krawtchouk case]\label{cor:additional}
For every $N\geq2$, $q>1$, and $0<r\leq1$, the recurrence \eqref{eq:parameters} has nonnegative linearization. In the normalization $R_0=1$, $R_1=x$, it is outside the Krawtchouk recurrence class.
\end{corollary}
\begin{proof}
Its increments are $d_i-d_{i-1}=q^{i-1}/[N]_q$, so all hypotheses hold. For a Krawtchouk recurrence in this normalization the increments of $b_i+c_i$ are constant. Here their ratio is $q>1$ and $N\geq2$, so they are not constant. An affine change of the support transporting the same endpoint-normalized basis leaves the multiplication coefficients in the basis unchanged; it cannot remove this distinction.
\end{proof}

\begin{proposition}[Relation to the existing algebraic construction]\label{prop:source}
The quadratic relations \eqref{eq:algebra} are those of Koelink~\cite[Theorem~3.1(ii), equation (3.3)]{koelink}, with $z_j=u(x^j)$ and the same parameters $p,q$. The recurrence in this paper is the normalized recurrence of his Theorem~7.1, with $r=1/p$; its polynomial-in-the-spectral-variable interpretation is the dual $q$-Krawtchouk interpretation described after his Theorem~7.8.
\end{proposition}
\begin{proof}
The source square relation is $u(x^j)^2=(q-1)u(x^j)\sum_{l>j}u(x^l)+(p-1)u(x^j)+pq^{N-j}$, which is \eqref{eq:algebra}. In Theorem~7.1 the coefficients of the next, current and previous indices are respectively $pq^i(1-q^{N-i})$, $(p-1)(1-q^i)$ and $1-q^i$. Division by $p(1-q^N)$ gives \eqref{eq:parameters} for $q>1$. For $0\leq f\leq N$, the corresponding spectral coordinate is
\[
x_f=\frac{p(1-q^{N-f})-(1-q^f)}{p(1-q^N)}
=\frac{q^{N-f}-rq^f+r-1}{q^N-1},\qquad r=1/p.
\]
Writing $\phi_f(w_d)$ for Koelink's spherical-function values, we have $R_d(x_f)=\phi_f(w_d)$ for $0\leq d\leq N$: the initial value is one and the normalized recurrences agree, so induction in $d$ identifies them.
As $q\to1$, dividing numerator and denominator by $q-1$ and using the finite geometric sums gives $x_f\to1-(1+r)f/N$.
The $q=1$ case follows directly from the construction above, without division by zero. His discussion after Theorem~7.8 explicitly interchanges polynomial degree and spectral index to obtain the dual family.
\end{proof}

The geometric criterion covers the full positive Krawtchouk range, including the symmetric endpoint. The perturbation criterion allows freely varying coefficients around each Krawtchouk array in the interior of the positive linearization range; its stated radius is conservative and decreases with $N$. Both hypotheses can be checked using a number of arithmetic comparisons proportional to $N$, without forming any general product coefficients or testing polynomial matrices. The proofs use positive algebra multiplication, a lower bound from a single positive term, and a norm estimate. They provide sufficient conditions, not a characterization of all finite systems with property (P). The geometric parameter family and underlying algebra predate Szwarc's survey; this paper makes no claim of historical priority for these constructions or criteria.

\section{Szwarc's quadratic system}\label{sec:szwarc}

Problem~2 of~\cite[\S5]{szwarc} does not stop at the Krawtchouk recurrence. With his parameter written as $p_0$, Szwarc introduces the symmetric recurrence of length $2N+1$
\begin{equation}\label{eq:szwarc-q}
yQ_{2n}=(N-n)Q_{2n+1}+nQ_{2n-1},\qquad
yQ_{2n-1}=(1-p_0)Q_{2n}+p_0Q_{2n-2},
\end{equation}
records that $Q_{2n}(y)$ is the Krawtchouk polynomial $K_n(y^2)$ of his recurrence, states that the $Q_n$ have nonnegative linearization for $p_0\leq1/2$, and asks for a general criterion that would handle this case. His Theorem~3.3 for infinite symmetric systems does not apply. In the normalization \eqref{eq:szwarc-q} its monotonicity hypotheses hold, and its hypothesis $\alpha_n\leq\gamma_n$ holds at odd indices exactly when $p_0\leq1/2$; at an even index $2n$ it reads $n\leq N-n$ and fails in the upper half. Some failure of this kind is forced in every finite system, whose terminal upward coefficient vanishes. This section proves the positivity of \eqref{eq:szwarc-q} by a graded version of the algebra of Section~\ref{sec:algebra}, and then gives an explicit coefficient criterion for symmetric finite systems near \eqref{eq:szwarc-q}.

Put $M=2N$, $R_{2n}(t)=Q_{2n}(\sqrt Nt)$ and $R_{2n-1}(t)=\sqrt N\,Q_{2n-1}(\sqrt Nt)$. Substitution in \eqref{eq:szwarc-q} shows that the $R_k$ satisfy \eqref{eq:recurrence}, with $N$ replaced by $M$, for the array
\begin{equation}\label{eq:qarray}
b_k=0,\qquad
(a_{2n},c_{2n})=\Big(\frac{N-n}{N},\frac nN\Big),\qquad
(a_{2n-1},c_{2n-1})=(1-p_0,\,p_0).
\end{equation}
It satisfies \eqref{eq:basic} with $M$ in place of $N$ whenever $0<p_0<1$. The two normalizations differ by positive factors and a positive dilation, so they have the same product coefficients up to positive factors.

\begin{theorem}[Szwarc's quadratic system]\label{thm:szwarc}
Let $N\geq1$ and $0<p_0\leq1/2$. The array \eqref{eq:qarray} has a symmetric positive orthogonality measure on $2N+1$ points, and for all $0\leq m,n\leq 2N$
\[
R_mR_n=\sum_{k=0}^{2N}g(m,n;k)R_k,\qquad g(m,n;k)\geq0,\qquad\sum_k g(m,n;k)=1
\]
on that support. If $1/2<p_0<1$, then $g(2,2;2)<0$.
\end{theorem}

Throughout this section put $r=p_0/(1-p_0)$, so that $0<r\leq1$ exactly when $p_0\leq1/2$. Let $A$ be the commutative algebra generated by $y_1,\ldots,y_N$ subject to $y_j^2=(1-r)y_j+r$. This is the algebra of Section~\ref{sec:algebra} with $q=1$ after the rescaling $y_j=z_j/p$ used in Lemma~\ref{lem:margin}. Its squarefree monomials $y_S$ form a basis, and for $r\leq1$ all multiplication coefficients are nonnegative. Call an element of $A$ nonnegative if its coefficients in this basis are nonnegative.

\begin{lemma}[Edge idempotents]\label{lem:edge}
For $1\leq l\leq N$ put $f_l=(r+y_l)/(1+r)$. Then $y_lf_l=f_l$ and $f_l^2=f_l$. The ideal $f_lA$ has basis $f_ly_S$, $S\subseteq\{1,\ldots,N\}\setminus\{l\}$, and $f_l u$ has nonnegative coefficients in this basis whenever $u\in A$ is nonnegative.
\end{lemma}
\begin{proof}
First $(1+r)y_lf_l=ry_l+(1-r)y_l+r=(1+r)f_l$. Then $(1+r)f_l^2=rf_l+y_lf_l=(1+r)f_l$. Let $A'$ be generated by the $y_j$ with $j\neq l$, so that $A=A'\oplus y_lA'$. Since $f_ly_l=f_l$, $f_lA=f_lA'$. The map $u\mapsto f_lu=(ru+y_lu)/(1+r)$ is injective on $A'$ by the direct sum, which gives the basis. For the last claim, $f_ly_S=f_ly_{S\setminus\{l\}}$ for every $S$.
\end{proof}

Let $V=A\oplus\bigoplus_{l=1}^Nf_lA$, on which $A$ acts by multiplication in every summand, and call a vector nonnegative if all of its coordinates are nonnegative in the bases above. Define the $A$-linear operator
\[
Y(u;v_1,\ldots,v_N)=\Big(\frac1N\sum_{l=1}^Nv_l\,;\,f_1u,\ldots,f_Nu\Big).
\]
Put $U_{2n}=\binom Nn^{-1}\sum_{|S|=n}y_S\in A$ for $0\leq n\leq N$. For $0\leq n\leq N-1$, let $U_{2n+1}$ be the vector in $\bigoplus_lf_lA$ whose $l$th coordinate is $\binom{N-1}n^{-1}\sum f_ly_S$, summed over $S\subseteq\{1,\ldots,N\}\setminus\{l\}$ with $|S|=n$.

\begin{lemma}[Three-term action]\label{lem:qthree}
With $U_{-1}=U_{2N+1}=0$ and the coefficients \eqref{eq:qarray}, $YU_k=a_kU_{k+1}+c_kU_{k-1}$ for $0\leq k\leq2N$.
\end{lemma}
\begin{proof}
The $l$th coordinate of $Y\sum_{|S|=n}y_S$ is $\sum_{S\not\ni l}f_ly_S+\sum_{S'\not\ni l}f_ly_{S'}$, with $|S|=n$ and $|S'|=n-1$, because $f_ly_S=f_ly_{S\setminus\{l\}}$. Dividing by $\binom Nn$ and using $\binom{N-1}n/\binom Nn=(N-n)/N$ and $\binom{N-1}{n-1}/\binom Nn=n/N$ gives the even case. For the odd case, $(1+r)f_ly_S=ry_S+y_{S\cup\{l\}}$ when $l\notin S$. Each $n$-set occurs for $N-n$ choices of $l$ and each $(n+1)$-set for $n+1$ choices, so
\[
YU_{2n+1}=\frac{r(N-n)\binom Nn U_{2n}+(n+1)\binom N{n+1}U_{2n+2}}{N(1+r)\binom{N-1}n}
=\frac{rU_{2n}+U_{2n+2}}{1+r}.
\]
Finally $r/(1+r)=p_0$ and $1/(1+r)=1-p_0$.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:szwarc}]
Lemma~\ref{lem:finite} gives a positive measure on the $2N+1$ zeros of the terminal polynomial $T(t)=tR_{2N}(t)-R_{2N-1}(t)$. Since $b\equiv0$, the matrix $J$ is conjugate to $-J$ by $\operatorname{diag}((-1)^i)$, which fixes $e_0$; hence the measure is symmetric and $R_k(-t)=(-1)^kR_k(t)$. Put $\Phi(f)=f(Y)U_0$, where $U_0=(1;0,\ldots,0)$. Lemma~\ref{lem:qthree} gives $\Phi(R_k)=U_k$ for $k\leq2N$ and $\Phi(T)=YU_{2N}-U_{2N-1}=0$. Every polynomial vanishing on the support is a multiple of $T$, so $\Phi$ maps it to zero. Hence the product identity on the support becomes
\[
R_m(Y)R_n(Y)U_0=\sum_kg(m,n;k)U_k.
\]
The supports of the $U_k$ in the bases of $V$ are nonempty and disjoint: $U_{2n}$ uses the $y_S$ with $|S|=n$, and $U_{2n+1}$ uses the $f_ly_S$ with $l\notin S$, $|S|=n$. Each basis vector lies in exactly one of them, with positive coefficient. Consequently $g(m,n;k)\geq0$ for every $k$ whenever the left side is nonnegative.

Suppose $m$ is even. Since polynomials in $Y$ commute and $Y$ is $A$-linear,
\[
R_m(Y)R_n(Y)U_0=R_n(Y)(U_mU_0)=U_m\,R_n(Y)U_0=U_mU_n.
\]
Here $U_m\in A$ and $U_n$ are nonnegative, so their product is nonnegative by the positivity of $A$ and Lemma~\ref{lem:edge}. The same holds when $n$ is even, since $g(m,n;k)=g(n,m;k)$. If $m,n$ are odd and $k$ is odd, then $g(m,n;k)=0$ by symmetry of the measure. If $m,n$ are odd and $k$ is even, then $g(m,n;k)\int R_k^2\,d\mu=\int R_mR_nR_k\,d\mu=g(k,m;n)\int R_n^2\,d\mu\geq0$. The point $t=1$ belongs to the support because $J\boldsymbol1=\boldsymbol1$, and $R_k(1)=1$, so the coefficients sum to one.

For $1/2<p_0<1$ we have $r>1$. The identities above are purely algebraic and remain valid, but $A$ is no longer positive. In particular $U_2^2=N^{-2}\big((1-r)\sum_jy_j+Nr+2\sum_{i<j}y_iy_j\big)$, whose $U_2$ coefficient $g(2,2;2)=(1-r)/N$ is negative.
\end{proof}

Since $Y^2$ acts on $A$ by multiplication by $N^{-1}\sum_lf_l=(r+X)/(1+r)$, with $X=N^{-1}\sum_ly_l$, the even part of the theorem is Corollary~\ref{cor:kraw}: $R_{2n}(t)=K_n\big((1+r)t^2-r\big)$ in the normalization of that corollary. Thus Theorem~\ref{thm:szwarc} recovers the full positive Krawtchouk range by Szwarc's quadratic route. At $p_0=1/2$ the operator $Y$ is the normalized adjacency operator of the subdivided $N$-cube seen from a vertex, and the theorem reduces to counting in that graph.

\begin{lemma}[Margin for the quadratic system]\label{lem:qmargin}
Let $0<p_0<1/2$ and $s=\min(r,1-r)$. For the array \eqref{eq:qarray},
\[
g(m,n;k)\geq(rs/8)^N\qquad\text{whenever }|m-n|\leq k\leq m+n\text{ and }m+n+k\text{ is even}.
\]
All other coefficients vanish.
\end{lemma}
\begin{proof}
The vanishing statements are Lemma~\ref{lem:finite} and the symmetry used above. We use $\binom Nk\leq2^N$ throughout. Up to the order of $m,n$, there are three cases.

If $m,n,k$ are even, the coefficient is a Krawtchouk coefficient computed in $A$, so Lemma~\ref{lem:margin} gives the lower bound $(s/4)^N\geq(rs/8)^N$.

Let $m=2a$, $n=2b+1$ and $k=2c+1$, so that
\[
\max(a-b-1,\,b-a)\leq c\leq\min(a+b,\,N-1).
\]
Fix $l$ and a set $U\not\ni l$ with $|U|=c$. The $l$th coordinate of $U_mU_n$ is
\[
\binom Na^{-1}\binom{N-1}b^{-1}\sum_{|T|=a}\ \sum_{S\not\ni l,\ |S|=b}f_l\,y_{T\setminus\{l\}}\,y_S .
\] Every nonzero term arising from a chosen reduction of $y_{T\setminus\{l\}}y_S$ is a product of at most $N-1$ factors from $\{r,1-r\}$, and therefore has coefficient at least $s^{N-1}$. Put $a'=|T\setminus\{l\}|$, which can equal $a-1$ when $a\geq1$ and $a$ when $a\leq N-1$. In the $N-1$ coordinates other than $l$, sets of sizes $a'$ and $b$ with overlap $o$, retaining the linear term on $t\leq o$ overlap coordinates, give monomials of size $a'+b-2o+t$. As $o$ ranges over its admissible values these sizes fill the interval $\big[|a'-b|,\min(a'+b,N-1)\big]$. The two admissible values of $a'$ cover every $c$ above. Hence $f_ly_U$ has coefficient at least $s^{N-1}\binom Na^{-1}\binom{N-1}b^{-1}$, and comparison with $U_k$ gives
\[
g(m,n;k)\geq\binom{N-1}c\frac{s^{N-1}}{\binom Na\binom{N-1}b}\geq\frac{2s^{N-1}}{4^N}\geq\Big(\frac s4\Big)^N.
\]

Finally let $m=2b+1$, $n=2c+1$ and $k=2a$. With $\pi_i$ as in the proof of Lemma~\ref{lem:finite}, \eqref{eq:qarray} gives $\pi_{2a}=\binom Nar^{-a}$ and $\pi_{2c+1}=\binom{N-1}cr^{-c}/p_0$. Orthogonality gives
\[
g(2b+1,2c+1;2a)=g(2a,2b+1;2c+1)\frac{\pi_{2a}}{\pi_{2c+1}}
\geq\frac{2s^{N-1}}{4^N}\cdot\frac{p_0r^N}{2^{N-1}}
\geq\frac{2s^{N-1}r^{N+1}}{8^N},
\]
using $r^{c-a}\geq r^N$ and $p_0\geq r/2$. Since $s\leq r$, the last quantity is at least $(rs/8)^N$.
\end{proof}

The proof of Theorem~\ref{thm:perturbation} uses only three properties of its reference: nonnegative linearization with sums one, a lower bound for the upward coefficients, and a margin on the known support. We record it in that generality.

\begin{lemma}[Stability of a reference with a margin]\label{lem:stability}
Let $a,b,c$ satisfy \eqref{eq:basic} on the indices $0,\ldots,M$, have nonnegative linearization, and satisfy $a_i\geq\alpha$ for $i<M$, where $0<\alpha\leq1$. Suppose $g(m,n;k)\geq\delta>0$ on a set $\Sigma$ of index triples. Let $\widetilde a,\widetilde b,\widetilde c$ satisfy \eqref{eq:basic}, with $\widetilde b_i\geq0$, and differ from $a,b,c$ by at most $\eta$ in every entry. If $\eta\leq\alpha/2$ and $\eta(8/\alpha)^M\leq\delta/2$, then $|\widetilde g(m,n;k)-g(m,n;k)|\leq\delta/2$ for all $m,n,k$; in particular $\widetilde g\geq\delta/2$ on $\Sigma$.
\end{lemma}
\begin{proof}
Repeat the proof of Theorem~\ref{thm:perturbation} with $N$ replaced by $M$. Now $\widetilde a_m\geq\alpha/2$, so the subtracted recurrences give $e_{m+1}\leq(4e_m+2e_{m-1}+12\eta)/\alpha$. With $L=8/\alpha\geq8$, induction gives $e_m\leq\eta L^m$: the base case is $e_1\leq3\eta$, and the step needs $4L^m+2L^{m-1}+12\leq8L^m$, which holds for $m\geq1$. Every entry of $\widetilde B_m-B_m$ is therefore at most $\eta L^M\leq\delta/2$, and \eqref{eq:matrix-product} identifies these entries with the product coefficients.
\end{proof}

Theorem~\ref{thm:perturbation} is the case $M=N$, $\alpha=1/N$ and $\delta=(s/4)^N$ of this lemma.

\begin{theorem}[Symmetric criterion near Szwarc's system]\label{thm:symmetric}
Let $N\geq1$, $0<p_0<1/2$, $r=p_0/(1-p_0)$, $s=\min(r,1-r)$, and
\[
\eta=\frac12\Big(\frac{rs}8\Big)^N(16N)^{-2N}.
\]
Let $c_k$ be the downward coefficients in \eqref{eq:qarray}. Take real numbers $\widetilde c_1,\ldots,\widetilde c_{2N-1}$ with $|\widetilde c_k-c_k|\leq\eta$, and put $\widetilde c_0=0$, $\widetilde c_{2N}=1$, $\widetilde b_k=0$ and $\widetilde a_k=1-\widetilde c_k$. The resulting symmetric finite system has nonnegative linearization with sums one. Moreover $\widetilde g(m,n;k)\geq\frac12(rs/8)^N$ whenever $|m-n|\leq k\leq m+n$ and $m+n+k$ is even, and $\widetilde g(m,n;k)=0$ otherwise.
\end{theorem}
\begin{proof}
The perturbed array satisfies \eqref{eq:basic} with $M=2N$: $\widetilde a_k\geq1/N-\eta>0$ for even $k<2N$, $\widetilde a_k\geq1/2-\eta>0$ for odd $k$, and $\widetilde c_k\geq\min(p_0,1/N)-\eta>0$ for $k>0$. Theorem~\ref{thm:szwarc} shows that the reference has nonnegative linearization, and $a_k\geq1/(2N)$ for $k<2N$. Lemma~\ref{lem:qmargin} gives the margin $\delta=(rs/8)^N$ on the stated set. Apply Lemma~\ref{lem:stability} with $\alpha=1/(2N)$: then $\eta\leq\alpha/2$ and $\eta(16N)^{2N}=\delta/2$. Off the stated set, $\widetilde g$ vanishes by Lemma~\ref{lem:finite} and by the symmetry of the perturbed measure, which holds because $\widetilde b\equiv0$. The sums equal one because $\widetilde R_m(1)=1$ and $1$ lies in the support.
\end{proof}

\begin{corollary}[Symmetric systems outside both families]\label{cor:symmetric-new}
For $N\geq2$, $0<p_0<1/2$ and $0<h\leq\eta$, the array obtained from \eqref{eq:qarray} by $c_1\mapsto p_0+h$, $a_1\mapsto1-p_0-h$ has nonnegative linearization. It is neither of the form \eqref{eq:qarray} nor of the form \eqref{eq:parameters}. More generally, Theorem~\ref{thm:symmetric} admits a relatively open set of symmetric stochastic arrays, with $2N-1$ free coefficients, around each array \eqref{eq:qarray} with $0<p_0<1/2$.
\end{corollary}
\begin{proof}
Theorem~\ref{thm:symmetric} applies. The odd downward coefficients $c_1=p_0+h$ and $c_3=p_0$ differ, so the array is not of the form \eqref{eq:qarray}; here $N\geq2$ ensures $3<2N$. In \eqref{eq:parameters}, on $2N+1$ indices, the downward coefficients $c_i=r[i]_q/[2N]_q$ are strictly increasing, whereas $c_3<c_1$.
\end{proof}

\paragraph{A criterion for all symmetric finite systems.}
Szwarc uses the quadratic transformation~\cite[\S3.5]{szwarc} to pass from a symmetric system to its even part. For finite systems the converse direction also works: positivity of a symmetric system follows from positivity of two nonsymmetric finite systems, both read off from its coefficients. Any criterion for nonsymmetric finite systems therefore becomes a criterion for symmetric ones.

\begin{theorem}[Quadratic decomposition]\label{thm:decomp}
Let $N\geq2$, and let $a_k,c_k$ $(0\leq k\leq2N)$ with $b\equiv0$ satisfy \eqref{eq:basic} with $2N$ in place of $N$. Put $a_k=c_k=0$ for $k\notin[0,2N]$, and define the even component
\[
\hat a_n=a_{2n}a_{2n+1},\quad \hat b_n=c_{2n}a_{2n-1}+a_{2n}c_{2n+1},\quad \hat c_n=c_{2n}c_{2n-1}\qquad(0\leq n\leq N)
\]
and the odd component
\[
\check a_n=a_{2n+1}a_{2n+2},\quad \check b_n=a_{2n+1}c_{2n+2}+c_{2n+1}a_{2n},\quad \check c_n=c_{2n+1}c_{2n}\qquad(0\leq n<N).
\]
After the affine normalization $(\hat a_n,\hat b_n,\hat c_n)\mapsto(\hat a_n,\hat b_n-\hat b_0,\hat c_n)/\hat a_0$, and likewise for the odd component, these arrays satisfy \eqref{eq:basic} on the indices $0,\ldots,N$ and $0,\ldots,N-1$. If both have nonnegative linearization, so does the symmetric array. More precisely, with $\hat g$ and $\check g$ the product coefficients of the components and terms with indices out of range omitted,
\[
g(2a,2b;2c)=\hat g(a,b;c),\qquad
g(2a,2b+1;2c+1)=a_{2a}\,\check g(a,b;c)+c_{2a}\,\check g(a-1,b;c),
\]
the coefficients with $m+n+k$ odd vanish, and $g(2a+1,2b+1;2c)\int R_{2c}^2\,d\mu=g(2c,2a+1;2b+1)\int R_{2b+1}^2\,d\mu$. Conversely, nonnegative linearization of the symmetric array implies that of its even component.
\end{theorem}
\begin{proof}
By symmetry $R_{2n}(t)=P_n(t^2)$ and $R_{2n+1}(t)=tL_n(t^2)$ for polynomials $P_n$, $L_n$ of degree $n$. Applying \eqref{eq:recurrence} twice gives, with $x=t^2$,
\[
xP_n=\hat a_nP_{n+1}+\hat b_nP_n+\hat c_nP_{n-1},\qquad
xL_n=\check a_nL_{n+1}+\check b_nL_n+\check c_nL_{n-1}.
\]
The row sums of the components equal $a_{2n}+c_{2n}=1$ and $a_{2n+1}+c_{2n+1}=1$; the coefficients $\hat a_n,\check a_n$ are positive below the last index and vanish there, and $\hat c_n,\check c_n>0$ for $n\geq1$. Hence the normalized arrays, which describe the same polynomials in the variable $(x-\hat b_0)/\hat a_0$ (respectively $(x-\check b_0)/\check a_0$), satisfy \eqref{eq:basic}. The terminal relation $tR_{2N}=c_{2N}R_{2N-1}$ on the support $\Sigma$ of the symmetric system, applied once and twice, gives the terminal relations of $P$ on $\{t^2:t\in\Sigma\}$ and of $L$ on $\{t^2:t\in\Sigma,\ t\neq0\}$. These sets have $N+1$ and $N$ points, because $\Sigma$ is symmetric with $2N+1$ points and contains $0$. By Lemma~\ref{lem:finite} they are the supports of the two components.

The identity $tR_{2n}=a_{2n}R_{2n+1}+c_{2n}R_{2n-1}$ gives $P_n=a_{2n}L_n+c_{2n}L_{n-1}$ on the support of $L$; for $n=N$ it is the terminal relation, with $a_{2N}=0$. Hence, on $\Sigma\setminus\{0\}$,
\[
R_{2a}R_{2b+1}=t\big(a_{2a}L_aL_b+c_{2a}L_{a-1}L_b\big)=\sum_c\big(a_{2a}\check g(a,b;c)+c_{2a}\check g(a-1,b;c)\big)R_{2c+1},
\]
and both sides vanish at $t=0$. Similarly $R_{2a}R_{2b}=(P_aP_b)(t^2)=\sum_c\hat g(a,b;c)R_{2c}$ on $\Sigma$. Uniqueness of expansions on $\Sigma$ gives the displayed formulas. The vanishing for $m+n+k$ odd and the relation for two odd indices follow from the symmetry of the measure and from $g(m,n;k)\int R_k^2\,d\mu=\int R_mR_nR_k\,d\mu$, exactly as in the proof of Theorem~\ref{thm:szwarc}. The converse holds because $\hat g(a,b;c)=g(2a,2b;2c)$.
\end{proof}

Combined with Theorem~\ref{thm:criterion}, the decomposition gives a parity-split criterion of the same shape as Szwarc's Theorem~3.3: separate conditions on the even-indexed and the odd-indexed coefficients.

\begin{corollary}[Parity-split criterion]\label{cor:parity}
Let $N\geq1$ and let a symmetric array $(b\equiv0)$ on the indices $0,\ldots,2N$ satisfy \eqref{eq:basic}. Suppose that
\begin{enumerate}
\item the odd downward coefficients are constant, $c_{2n+1}=p_0$, with $0<p_0\leq1/2$;
\item the even downward coefficients $d_n=c_{2n}$ have positive increments $d_n-d_{n-1}$, $1\leq n\leq N$, forming a geometric progression with ratio $q\geq1$.
\end{enumerate}
Then the array has nonnegative linearization. With $r=p_0/(1-p_0)$ and $N\geq2$, its normalized even and odd components are \eqref{eq:parameters} with parameters $(N,q,r)$ and $(N-1,q,r/q)$, respectively. For $N=1$ the odd component consists only of $L_0=1$, the array is \eqref{eq:qarray}, and positivity follows directly from Theorem~\ref{thm:szwarc}. If $1/2<p_0<1$ in (i) and (ii) holds, then $g(2,2;2)<0$.
\end{corollary}
\begin{proof}
For $N=1$ this is Theorem~\ref{thm:szwarc}. Let $N\geq2$. The even component has $\hat a_n=(1-d_n)(1-p_0)$, $\hat b_n=d_n(1-p_0)+(1-d_n)p_0$ and $\hat c_n=d_np_0$, so $\hat a_0=1-p_0$, $\hat b_0=p_0$, and its normalization is $(1-d_n,\,(1-r)d_n,\,rd_n)$. This satisfies Theorem~\ref{thm:criterion} with $\beta=(1-r)/r\geq0$. For the odd component, $\check a_n=(1-p_0)(1-d_{n+1})$, $\check b_n=(1-p_0)d_{n+1}+p_0(1-d_n)$ and $\check c_n=p_0d_n$. Geometric increments give $d_{n+1}-d_1=qd_n$, so the normalization is
\[
\Big(\frac{1-d_{n+1}}{1-d_1},\ \frac{(q-r)d_n}{1-d_1},\ \frac{rd_n}{1-d_1}\Big).
\]
Its ratio $\beta=(q-r)/r$ is constant and nonnegative, and its profile $qd_n/(1-d_1)$ has geometric increments with ratio $q$. Theorem~\ref{thm:criterion} applies to both components, and Theorem~\ref{thm:decomp} concludes. Lemma~\ref{lem:parameters} identifies the parameters. For $p_0>1/2$, $g(2,2;2)=\hat g(1,1;1)$ is the normalized diagonal coefficient $(1-r)d_1<0$ (for $N=1$ see Theorem~\ref{thm:szwarc}).
\end{proof}

With $q=1$ the corollary is Szwarc's system \eqref{eq:qarray}, and it recovers Theorem~\ref{thm:szwarc}, including the Krawtchouk polynomials as its even component. For $q>1$ it gives a three-parameter family of symmetric finite systems with nonnegative linearization whose even components are the dual $q$-Krawtchouk arrays of Corollary~\ref{cor:additional}. Theorem~\ref{thm:decomp} also transfers the perturbation criteria: a symmetric array has nonnegative linearization whenever its two normalized components satisfy the hypotheses of Theorem~\ref{thm:perturbation}, or those of Lemma~\ref{lem:stability} around a reference with a margin, provided the set $\Sigma$ of that lemma contains every coefficient that can be nonzero for the perturbed components, or the remaining coefficients are separately known to stay nonnegative. Lemma~\ref{lem:stability} controls only $\Sigma$: for example, changing $K_{2,1}$ to $c_1=\tfrac12+\varepsilon$, $a_1=\tfrac12-\varepsilon$ gives $g(2,2;2)<0$ for every $\varepsilon>0$, although the positive coefficients of $K_{2,1}$ stay positive. Conversely, the even component of every array admitted by Theorem~\ref{thm:symmetric} is a nonsymmetric finite system with nonnegative linearization.

\paragraph{Products of low total degree.}
Szwarc's inequality method~\cite[Theorems~3.2 and~3.4]{szwarc} survives the passage to finite systems for all products whose two factors have total degree at most $N$. Only the terminal coefficients are excluded from its hypotheses. Write a finite system in a positive renormalization $P_n=R_n/\sigma_n$ $(\sigma_0=1)$ as $xP_n=\gamma_nP_{n+1}+\beta_nP_n+\alpha_nP_{n-1}$, so that $\gamma_n=a_n\sigma_{n+1}/\sigma_n$, $\beta_n=b_n$, $\alpha_n=c_n\sigma_{n-1}/\sigma_n$ and $\gamma_N=0$.

\begin{theorem}[Low products]\label{thm:low}
Let $a,b,c$ satisfy \eqref{eq:basic}. Suppose that for some positive $\sigma$,
\begin{enumerate}
\item $\beta_n$ is nondecreasing for $0\leq n\leq N-1$, and $\alpha_n$ is nondecreasing for $0\leq n\leq N$;
\item $\alpha_n+\gamma_n$ is nondecreasing for $0\leq n\leq N-2$;
\item $\gamma_i\geq\alpha_j$ whenever $0\leq j\leq i$ and $i+j\leq N-2$.
\end{enumerate}
Then $g(n,m;k)\geq0$ whenever $n+m\leq N$. Consequently a product coefficient can be negative only for a triple $(n,m,k)$ in which each two indices have sum greater than $N$.
\end{theorem}
\begin{proof}
Coefficients in two positive normalizations differ by positive factors, so we may work with the polynomials $\widetilde P_n$ of~\cite[(3.9)]{szwarc}, which satisfy $x\widetilde P_n=\alpha_{n+1}\widetilde P_{n+1}+\beta_n\widetilde P_n+\gamma_{n-1}\widetilde P_{n-1}$ with $\alpha_{N+1}=0$. Fix $k$ and let $u(n,m)$ be the coefficient of $\widetilde P_k$ in $\widetilde P_n\widetilde P_m$. Multiplying the product by $x$ in the two ways shows $Hu=0$ at every point of $\{0,\ldots,N\}^2$, where $H=L_1-L_2$ is the operator of~\cite[\S3.4]{szwarc} built from these coefficients, and $u(n,0)=\boldsymbol1_{n=k}$, $u(n,m)=u(m,n)$.

We prove $u(n,m)\geq0$ for $n\geq m$, $n+m\leq N$, by induction on $m$, following~\cite[Theorem~3.4]{szwarc}. Let $v$ be the indicator of the points $(i,j)$ with $j<m$, $|i-n|<m-j$ and $n+m-i-j$ odd. Every point in the support of $v$ satisfies $j<i$ and $i+j\leq n+m-1\leq N-1$, so $\langle Hu,v\rangle=0$ involves only rows where the finite recurrence holds. Hence $0=\langle u,H^*v\rangle$, and every point in the support of $H^*v$ has $i+j\leq n+m\leq N$. With $\alpha_0=0$ and $v$ set to zero outside its support, transposition gives
\[
(H^*v)(i,j)=\alpha_iv(i-1,j)+\gamma_iv(i+1,j)+(\beta_i-\beta_j)v(i,j)-\alpha_jv(i,j-1)-\gamma_jv(i,j+1),
\]
as in~\cite[\S3.4]{szwarc}. At $(n,m)$ it is $-\alpha_m<0$. At the other points it is one of
\[
\beta_i-\beta_j,\quad (\alpha_i+\gamma_i)-(\alpha_j+\gamma_j),\quad \alpha_i-\alpha_j,\quad \gamma_i-\alpha_j,
\]
with $j\leq i$. The first occurs only for $i\leq N-1$. The second occurs only at interior points, where $i+j\leq n+m-2\leq N-2$. The third occurs on the edge $i+j=n+m$. The last occurs on the edge $i-j=n-m$, where $i+j\leq N-2$. Hypotheses (i)--(iii) make all of these nonnegative, and all such points have second coordinate less than $m$. By the induction hypothesis and $u(i,0)\geq0$, $\alpha_mu(n,m)=\sum_{(i,j)\neq(n,m)}(H^*v)(i,j)u(i,j)\geq0$. For the last statement, $g(n,m;k)$, $g(n,k;m)$ and $g(m,k;n)$ are positive multiples of $\int R_nR_mR_k\,d\mu$.
\end{proof}

\begin{corollary}[Convex profiles]\label{cor:convex-low}
Let $b_i=(1-r)d_i$, $c_i=rd_i$, $a_i=1-d_i$ with $0<r\leq1$ and a convex profile $0=d_0<d_1<\cdots<d_N=1$, that is, with nondecreasing increments. Then $g(n,m;k)\geq0$ whenever two of $n,m,k$ have sum at most $N$. This includes every array \eqref{eq:parameters}.
\end{corollary}
\begin{proof}
Take $\sigma_n=r^{n/2}$. Then $\alpha_n=\sqrt r\,d_n$ and $\gamma_n=\sqrt r\,(1-d_n)$, so $\alpha$ and $\beta=(1-r)d$ are nondecreasing and $\alpha_n+\gamma_n=\sqrt r$ is constant. Convexity and $d_0=0$ give $d_i+d_j\leq d_{i+j}$, so $\gamma_i-\alpha_j=\sqrt r\,(1-d_i-d_j)\geq\sqrt r\,(1-d_{i+j})>0$ for $i+j\leq N-2$. Theorem~\ref{thm:low} applies.
\end{proof}

For such profiles, positivity can therefore fail only on triples with all pairwise sums above $N$. The convex counterexamples recorded in Section~\ref{sec:open} fail at $(N,N,N)$, which is such a triple.

\paragraph{Deep triples and reversal.}
Call $(n,m,k)$ deep if each two of its indices have sum greater than $N$. The reversed array $a'_i=c_{N-i}$, $b'_i=b_{N-i}$, $c'_i=a_{N-i}$ need not satisfy $a'_0=1$, $b'_0=0$. Its polynomials $R'_i$ are defined by the reversed recurrence from $R'_0=1$, so $R'_1=(x-b_N)/c_N$, and they still satisfy $R'_i(1)=1$; its matrix is $\Pi J\Pi$, where $\Pi$ reverses the order of the indices. Write $g'$ for its product coefficients.

\begin{lemma}[Reversal identity]\label{lem:reversal}
On the support, $R_NR'_t=R_{N-t}$ for $0\leq t\leq N$.
\end{lemma}
\begin{proof}
From $e_0^{\mathsf T}R_i(J)=e_i^{\mathsf T}$ for the array and for its reversal, $e_N^{\mathsf T}R'_t(J)=e_{N-t}^{\mathsf T}$. Hence $e_0^{\mathsf T}R_N(J)R'_t(J)=e_N^{\mathsf T}R'_t(J)=e_0^{\mathsf T}R_{N-t}(J)$. Both matrices commute with $J$ and $e_0$ is cyclic, so $R_N(J)R'_t(J)=R_{N-t}(J)$, which is the claim on the spectrum.
\end{proof}

\begin{theorem}[Deep reduction]\label{thm:deep}
For every array satisfying \eqref{eq:basic} and every deep triple $(x,y,z)$,
\[
g(x,y;z)=\sum_{t=0}^Ng'(N-x,N-y;t)\,g(N,N-t;z).
\]
Moreover $g(N,N;N-l)$ is the coefficient of $R'_l$ in $R_N$. Hence all coefficients are nonnegative if (a) $g\geq0$ on non-deep triples, (b) $g'(i,j;t)\geq0$ whenever $i+j<N$, and (c) $R_N$ is a nonnegative combination of $R'_0,\ldots,R'_N$.
\end{theorem}
\begin{proof}
By Lemma~\ref{lem:reversal}, $R_x=R_NR'_{N-x}$ and $R_y=R_NR'_{N-y}$ on the support. Expanding $R'_{N-x}R'_{N-y}=\sum_tg'(N-x,N-y;t)R'_t$ and using Lemma~\ref{lem:reversal} again gives $R_xR_y=\sum_tg'(N-x,N-y;t)R_NR_{N-t}$. Expanding $R_NR_{N-t}$ gives the formula. Writing $R_N=\sum_le_lR'_l$, Lemma~\ref{lem:reversal} gives $R_N^2=\sum_le_lR_{N-l}$, so $e_l=g(N,N;N-l)$. For the last statement, $(N-x)+(N-y)<N$, so (b) makes the weights $g'$ nonnegative. It remains to see $g(N,n;z)\geq0$. If $(N,n,z)$ is not deep this is (a). Otherwise $n+z>N$, and $g(N,n;z)$ is a positive multiple of $g(n,z;N)=\sum_tg'(N-n,N-z;t)\,g(N,N-t;N)$; here $g(N,N-t;N)$ is a positive multiple of $g(N,N;N-t)$, which is nonnegative by (c).
\end{proof}

\begin{theorem}[Palindromic criterion]\label{thm:palindromic}
Let $a,b,c$ satisfy \eqref{eq:basic} with $a_n=c_{N-n}$ and $b_n=b_{N-n}$ for all $n$, and satisfy the hypotheses of Theorem~\ref{thm:low} for some positive $\sigma$. Then the system has nonnegative linearization.
\end{theorem}
\begin{proof}
The reversed array equals the array, so $R'=R$ and $g'=g$. Theorem~\ref{thm:low} gives $g\geq0$ on all non-deep triples, in particular $g'(i,j;t)\geq0$ for $i+j<N$. Since $R_N=R'_N$ is a single reversed polynomial, $g(N,N;\cdot)\geq0$. Theorem~\ref{thm:deep} gives the deep triples.
\end{proof}

\begin{corollary}[Monotone palindromic systems]\label{cor:palin}
Let $b\equiv0$, $a_n=1-c_n$, and let $0=c_0<c_1\leq c_2\leq\cdots\leq c_N=1$ satisfy $c_n+c_{N-n}=1$. Then the system has nonnegative linearization. This includes the symmetric Krawtchouk array $c_n=n/N$.
\end{corollary}
\begin{proof}
The array is palindromic. With $\sigma\equiv1$, $\alpha_n=c_n$ is nondecreasing, $\beta\equiv0$ and $\alpha_n+\gamma_n=1$. If $j\leq i$ and $i+j\leq N-2$, then $j<N-i$, so $\alpha_j=c_j\leq c_{N-i}=1-c_i=\gamma_i$. Theorem~\ref{thm:palindromic} applies.
\end{proof}

Within the palindromic subclass $b\equiv0$, $c_n+c_{N-n}=1$, the hypotheses of Corollary~\ref{cor:palin} are monotonicity inequalities. They contain the symmetric Krawtchouk endpoint, where the perturbation criterion of Section~\ref{sec:perturbation} gives no neighbourhood and where the convex counterexamples of Section~\ref{sec:open} show that convexity alone does not suffice.

Combined with Theorem~\ref{thm:decomp}, Corollary~\ref{cor:palin} gives an inequality criterion for symmetric systems: an array with $b\equiv0$ on $0,\ldots,2N$ has nonnegative linearization whenever its two normalized components satisfy the hypotheses of Corollary~\ref{cor:palin}. For Szwarc's system \eqref{eq:qarray} at $p_0=1/2$ the components are the symmetric Krawtchouk arrays on $N+1$ and $N$ points (Corollary~\ref{cor:parity} with $q=r=1$), so this case is covered by monotonicity inequalities within the palindromic subclass.

The reversal route cannot reach systems whose diagonal increases at the top once $N\geq3$. If $b_{N-1}<b_N$, the reversed array has $g'(1,1;1)=(b'_1-b'_0)/a'_0=(b_{N-1}-b_N)/c_N<0$, and condition (b) of Theorem~\ref{thm:deep} requires $g'(1,1;1)\geq0$ when $1+1<N$. In particular it fails for the Krawtchouk arrays with $r<1$ and $N\geq3$. Szwarc's array \eqref{eq:qarray} has $b\equiv0$, so this argument does not apply to it. Its reversal replaces $p_0$ by $1-p_0$ and gives $g'(2,2;2)=(2p_0-1)/(Np_0)<0$ for $p_0<1/2$, which violates condition (b) for the array of length $2N+1$ when $4<2N$, that is, $N\geq3$. Miclo's palindromic criterion~\cite[Theorem~31]{miclo2015} requires $2^nP(n,n+1)$ to be nonincreasing on $[0,N/2]$, which the symmetric Krawtchouk chain violates for $N>2$.

\section{Limits of inequality criteria}\label{sec:limits}

Theorems~\ref{thm:low} and~\ref{thm:palindromic} control every triple except the deep ones by inequalities, and Section~\ref{sec:open} records shape conditions that fail on deep triples. This section shows that part of the failure is structural near the symmetric endpoint. For uniformly sampled polynomial deformation directions, and for the analytic and boundary-layer extensions specified below, admission at every sufficiently large symmetric Krawtchouk system imposes two first-order boundary equalities. This does not exclude arbitrary uniform inequality criteria, nor families of admissible arrays that are not of these forms. Write $K_{N,r}$ for the Krawtchouk array \eqref{eq:parameters} with $q=1$, and use the coordinates $b_1,\ldots,b_{N-1},c_1,\ldots,c_N$ of a stochastic array with $b_0=0$, $a_0=1$, $a_N=0$, $b_N=1-c_N$ and $a_n=1-b_n-c_n$ otherwise. An affine change of $x$, together with the positive normalization $R_n(x_0)=1$ at the largest support point $x_0$, reduces every finite system to this form. A direction $v=(\delta b_1,\ldots,\delta b_{N-1},\delta c_1,\ldots,\delta c_N)$ changes these coordinates; we put $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$.

\begin{lemma}[Corner value]\label{lem:corner-value}
For $0<r\leq1$, the array $K_{N,r}$ has $g(N,N;N)=(1-r)^N$.
\end{lemma}
\begin{proof}
In the model of Lemma~\ref{lem:margin}, $U_N=y_1\cdots y_N$ is the only normalized basis element containing $y_{\{1,\ldots,N\}}$, and $U_N^2=\prod_i\bigl((1-r)y_i+r\bigr)$ has coefficient $(1-r)^N$ at that monomial.
\end{proof}

Thus the corner coefficient vanishes at $r=1$, where it is a structural zero, together with the other perimeter and parity zeros of the palindromic array. The next lemma computes its first-order change exactly.

\begin{lemma}[Corner identity]\label{lem:corner}
Let $N\geq2$ and $s_N=(-1)^{\lfloor N/2\rfloor+1}\binom{N-1}{\lfloor(N-1)/2\rfloor}^{-1}$. Put $F=\delta b+2\delta c$ if $N$ is even and $F=\delta b$ if $N$ is odd. Then
\[
\frac{d}{d\varepsilon}\,g(N,N;N)\Big|_{K_{N,1}+\varepsilon v,\ \varepsilon=0}=s_N\sum_{n=0}^N(-1)^n\binom NnF(n).
\]
\end{lemma}
\begin{proof}
At $K_{N,1}$ the nodes are $\lambda_j=1-2j/N$, with masses $w_j=2^{-N}\binom Nj$ and $\pi_n=\binom Nn$ in Lemma~\ref{lem:finite}. Moreover $\binom Nn R_n(\lambda_j)$ is the binary Krawtchouk polynomial, so that
\begin{equation}\label{eq:kraw-gf}
\sum_{j=0}^N w_jR_n(\lambda_j)s^j=2^{-N}(1+s)^{N-n}(1-s)^n.
\end{equation}
The vectors $u_j=(R_n(\lambda_j))_n$ and $v_j=(w_j\pi_nR_n(\lambda_j))_n$ are right and left eigenvectors of $J$ with $v_i^\mathsf Tu_j=\boldsymbol1_{i=j}$. Since $R_N(\lambda_j)=(-1)^j$, the matrix $\Pi=R_N(J)$ reverses the indices. Let $J_\varepsilon=J+\varepsilon E$ be the perturbed recurrence matrix and $R_N^\varepsilon$ the perturbed polynomial. The matrix $R_N^\varepsilon(J_\varepsilon)$ commutes with $J_\varepsilon$ and has first row $e_N^\mathsf T$, by \eqref{eq:matrix-product}. Its derivative $X$ at $\varepsilon=0$ therefore satisfies $[J,X]=[\Pi,E]$ and $e_0^\mathsf TX=0$. In the eigenbasis, $\widehat X_{ij}=v_i^\mathsf TXu_j$ equals $((-1)^i-(-1)^j)\widehat E_{ij}/(\lambda_i-\lambda_j)$ for $i\neq j$, where $\widehat E_{ij}=v_i^\mathsf TEu_j$, and $\sum_i\widehat X_{ij}=0$. By \eqref{eq:matrix-product}, and since $\pi_N=1$, the derivative in the lemma is $h_N:=e_N^\mathsf TXe_N=\sum_{i,j}(-1)^{i+j}\widehat X_{ij}w_j$. Eliminating $\widehat X_{jj}$ gives
\[
h_N=-2\sum_{i+j\ \mathrm{odd}}\widehat X_{ij}w_j=N\sum_{i\neq j}\widehat E_{ij}w_j\frac{(-1)^i-(-1)^j}{i-j}.
\]
Perturbing row $n$ alone means $E=e_n\rho^\mathsf T$ and $\widehat E_{ij}=w_i\pi_nR_n(\lambda_i)\,\rho^\mathsf Tu_j$. Write $\mathrm i$ for the imaginary unit and insert
\[
\frac{(-1)^i-(-1)^j}{i-j}=-\pi\int_0^1\sin\pi\bigl(\theta i+(1-\theta)j\bigr)\,d\theta,
\]
which also vanishes for $i=j$. Then
\begin{gather*}
h_N=-\pi N\pi_n\int_0^1\operatorname{Im}\bigl(A(\theta)B(\theta)\bigr)\,d\theta,\\
A=\sum_iw_iR_n(\lambda_i)e^{\mathrm i\pi\theta i},\qquad
B=\sum_jw_j(\rho^\mathsf Tu_j)e^{\mathrm i\pi(1-\theta)j},
\end{gather*}
and both sums are given by \eqref{eq:kraw-gf}. Put $\phi=\pi\theta/2$.
\begin{itemize}
\item Coordinate $b_n$, $1\leq n<N$, so $\rho=e_n-e_{n+1}$. Then
\[
AB=-(-1)^n\,\mathrm i^{N-1}\cos^N\!\phi\,\sin^{N-1}\!\phi\,e^{-\mathrm i\phi},
\]
and $h_N=s_N(-1)^n\binom Nn$. The integral reduces to $\int_0^{\pi/2}\cos^{N+1}\!\phi\,\sin^{N-1}\!\phi\,d\phi$ ($N$ even) or $\int_0^{\pi/2}\cos^{N}\!\phi\,\sin^{N}\!\phi\,d\phi$ ($N$ odd), and each equals $|s_N|/(2N)$.
\item Coordinate $c_n$, $1\leq n<N$, so $\rho=e_{n-1}-e_{n+1}$. Now $B$ acquires the factor $e^{\mathrm i\phi}/\cos\phi$, and the integrand carries $\sin((N-1)\pi/2)$. The contribution vanishes for odd $N$. For even $N$ it is twice that of $b_n$, since the two beta integrals have ratio $2$.
\item Coordinate $c_N$, so $\rho=e_{N-1}-e_N$ in row $N$. The same computation with $n=N$ gives $s_N$.
\end{itemize}
Summing these contributions with the conventions $\delta b_0=\delta c_0=0$ and $\delta b_N=-\delta c_N$ gives the stated alternating sum.
\end{proof}

\begin{definition}\label{def:rule}
A \emph{uniform rule} is a pair of real functions $\beta,\gamma$ on $[0,1]$. It defines, for each $N$, the direction $v_N$ with $\delta b_n=\beta(n/N)$ for $1\leq n<N$ and $\delta c_n=\gamma(n/N)$ for $1\leq n\leq N$. A set of arrays \emph{admits} the rule at the symmetric endpoint if there is $N_0$ such that for every $N\geq N_0$ there is $\varepsilon_N>0$ with $K_{N,1}+\varepsilon v_N$ in the set for all $0<\varepsilon<\varepsilon_N$. Put
\[
L_{\mathrm{even}}=\beta(0)+2\gamma(0)+\beta(1)+\gamma(1),\qquad L_{\mathrm{odd}}=\beta(0)-\beta(1)-\gamma(1).
\]
\end{definition}

\begin{theorem}[Forced equalities for uniform criteria]\label{thm:uniform}
Let $\beta,\gamma$ be polynomials. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. If $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$, the first-order change of $g(N,N;N)$ along $v_N$ vanishes for every $N$ above the degrees of $\beta$ and $\gamma$.
\end{theorem}
\begin{proof}
For a polynomial $p$ of degree less than $N$, $\sum_{n=0}^N(-1)^n\binom Nnp(n/N)=0$. Only boundary terms survive in Lemma~\ref{lem:corner}: the derivative equals $-s_NL_{\mathrm{even}}$ for even $N$ and $-s_NL_{\mathrm{odd}}$ for odd $N$. The sign of $s_N$ changes from $N$ to $N+2$. If, for instance, $L_{\mathrm{even}}\neq0$, then the derivative is negative for every large even $N$ in one residue class modulo $4$. For such $N$, $g(N,N;N)<0$ at $K_{N,1}+\varepsilon v_N$ for all small $\varepsilon>0$, since the coefficient vanishes at $\varepsilon=0$.
\end{proof}

The known positive deformations satisfy both equalities: the Krawtchouk direction $\beta(x)=x$, $\gamma(x)=-x$, palindromic deformations with $\beta=0$, $\gamma$ odd about $\tfrac12$ and $\gamma(0)=\gamma(1)=0$ (Corollary~\ref{cor:palin}), and the tangent direction $\beta=0$, $\gamma(x)=x(x-1)$ of the geometric family at $q=1$ (Theorem~\ref{thm:criterion}). The two functionals are independent already on constant rules, where $L_{\mathrm{even}}=2\beta+3\gamma$ and $L_{\mathrm{odd}}=-\gamma$. Consequently, for every $d\geq0$, no set of arrays with property (P) admits all rules of an open subset of the polynomial rules of degree at most $d$. In this sense, a criterion that admits the symmetric Krawtchouk systems through polynomial uniform rules must impose the two equalities on them. The geometric criterion and Corollary~\ref{cor:palin} are of this mixed type.

The polynomial hypothesis can be replaced by analyticity on a fixed region. Let $U(x)=\int_0^1\log|x-t|\,dt$ and $\Omega=\{x\in\mathbb C:U(x)\leq-1\}$, the region of convergence of equispaced interpolation. It contains $[0,1]$, has nonanalytic boundary points (with vertical tangents) at $0$ and $1$, and meets the line $\operatorname{Re}x=\tfrac12$ at $\operatorname{Im}x=\pm0.2628\ldots$.

\begin{lemma}[N\"orlund--Rice bound]\label{lem:nr}
If $f$ is analytic on an open set containing $\Omega$, then $\sum_{n=0}^N(-1)^n\binom Nnf(n/N)=O(\sqrt N\,e^{-\eta N})$ for some $\eta>0$.
\end{lemma}
\begin{proof}
The residues of $1/\prod_{k=0}^N(x-k/N)$ give
\[
\sum_{n=0}^N(-1)^n\binom Nnf(n/N)=(-1)^N\frac{N!}{N^N}\,\frac1{2\pi i}\oint_\Gamma\frac{f(x)\,dx}{\prod_{k=0}^N(x-k/N)}
\]
for any cycle $\Gamma$ in the domain of $f$ that winds once around $[0,1]$. Since $U$ is continuous and tends to $\infty$, the compact sets $\{U\leq-1+t\}$ shrink to $\Omega$ as $t\downarrow0$. Choose $\eta>0$ with $\{U\leq-1+3\eta\}$ inside the domain of $f$, and a bounded polygonal open set $V$ with $\{U\leq-1+\eta\}\subset V$ and $\overline V\subset\{U<-1+3\eta\}$. The oriented boundary $\Gamma$ of $V$, possibly with several components, is a cycle outside $\{U\leq-1+\eta\}$ that winds once around every node $k/N$ and bounds a region inside the domain of $f$. With $d=\operatorname{dist}(\Gamma,[0,1])>0$, the derivative of $t\mapsto\log|x-t|$ on $[0,1]$ is bounded by $1/d$ for $x\in\Gamma$, so a Riemann-sum estimate gives $\sum_{k=0}^N\log|x-k/N|\geq NU(x)-C_\Gamma\geq N(-1+\eta)-C_\Gamma$ with $C_\Gamma$ independent of $N$. Stirling's bound $N!/N^N\leq e\sqrt Ne^{-N}$ completes the proof.
\end{proof}

\begin{corollary}\label{cor:analytic-rules}
Let $\beta,\gamma$ be analytic on an open set containing $\Omega$. If a set of arrays with property (P) admits the rule $(\beta,\gamma)$ at the symmetric endpoint, then $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$. When these equalities hold, the first-order change of $g(N,N;N)$ along $v_N$ is $O(|s_N|\sqrt N\,e^{-\eta N})$; it need not vanish.
\end{corollary}
\begin{proof}
By Lemma~\ref{lem:nr}, the alternating sum of $\beta+2\gamma$ or $\beta$ is $O(\sqrt Ne^{-\eta N})$. The derivative in Lemma~\ref{lem:corner} is therefore $s_N(-L_{\mathrm{even}}+o(1))$ for even $N$ and $s_N(-L_{\mathrm{odd}}+o(1))$ for odd $N$, and the argument of Theorem~\ref{thm:uniform} gives the equalities. The rule $\beta(x)=e^x-1-(e-1)x$, $\gamma=0$ has $L_{\mathrm{even}}=L_{\mathrm{odd}}=0$ and derivative $s_N(1-e^{1/N})^N\neq0$.
\end{proof}

Deformations may also depend on $N$ in other ways. For a single $N$ the corner gives only one inequality. For $N\leq10$, exact computation finds a direction with strictly positive first-order change at every structural zero of $K_{N,1}$, and the arrays $K_{N,1}+\varepsilon v$ have property (P) for $\varepsilon=10^{-3}$ and $10^{-5}$; whether such directions exist for every $N$ is not proved here. The corner nevertheless constrains families that are regular in $N$.

\begin{proposition}[Families depending on $N$]\label{prop:families}
Let $v_N$ be directions such that a set with property (P) contains $K_{N,1}+\varepsilon v_N$ for all large $N$ and small $\varepsilon>0$, and let $A_N$ be the alternating sum in Lemma~\ref{lem:corner} for $v_N$. Then $s_NA_N\geq0$ for all large $N$.
\begin{enumerate}
\item Along either parity class, $A_N$ is not eventually strictly positive and not eventually strictly negative. If $A_N$ has an eventual weak sign along a parity class, it vanishes for all large $N$ of the residue class modulo $4$ on which that sign conflicts with the sign of $s_N$.
\item Suppose $\delta b_n=\beta(n/N)+p_n+q_{N-n}$ and $\delta c_n=\gamma(n/N)+p'_n+q'_{N-n}$, with $\beta,\gamma$ as in Corollary~\ref{cor:analytic-rules} and finitely supported boundary layers $p,q,p',q'$ independent of $N$. Then $q'_0=L_{\mathrm{even}}=L_{\mathrm{odd}}$, $p_k=q_k$ and $p'_k+q'_k=-p_k$ for $k\geq1$.
\end{enumerate}
\end{proposition}
\begin{proof}
A negative first-order change of $g(N,N;N)$ excludes $K_{N,1}+\varepsilon v_N$ for small $\varepsilon$, so $s_NA_N\geq0$. Part (1) follows because the sign of $s_N$ alternates along each parity class. In (2), write $D_Nf=\sum_{n=0}^N(-1)^n\binom Nnf(n/N)$. For large $N$, $A_N=D_N(\beta+2\gamma)+P_e(N)$ for even $N$ and $A_N=D_N\beta+P_o(N)$ for odd $N$, where
\begin{gather*}
P_e(N)=q'_0-L_{\mathrm{even}}+\sum_{k\geq1}(-1)^k\binom Nk\bigl[p_k+q_k+2(p'_k+q'_k)\bigr],\\
P_o(N)=q'_0-L_{\mathrm{odd}}+\sum_{k\geq1}(-1)^k\binom Nk(p_k-q_k).
\end{gather*}
These are polynomials in $N$. A nonzero polynomial has an eventual strict sign, which the remainder $O(\sqrt Ne^{-\eta N})$ of Lemma~\ref{lem:nr} cannot change, so part (1) forces $P_e\equiv P_o\equiv0$. The polynomials $1,\binom N1,\binom N2,\ldots$ are linearly independent, which gives the stated conditions.
\end{proof}

Thus a separate adjustment of the top coefficient $c_N$ reduces the two bulk equalities to the single equality $\gamma(0)+\beta(1)+\gamma(1)=0$. The boundary layers must be palindromic to first order. Families not covered by part~(1) must have $A_N$ change sign, or vanish, infinitely often within a parity class.

Criteria that cover $r<1$ but not $r=1$ are thin near $r=1$.

\begin{proposition}[Thinness near the symmetric endpoint]\label{prop:thin}
Fix $N\geq2$ and a direction $v$ along which the first-order change $\dot g$ of $g(N,N;N)$ at $K_{N,1}$ is negative. There are $r_*<1$ and $C,c>0$ such that $K_{N,r}+\varepsilon v$ lacks property (P) whenever $r_*<r<1$ and $C(1-r)^N\leq\varepsilon\leq c$.
\end{proposition}
\begin{proof}
The function $G(r,\varepsilon)=g(N,N;N)$ at $K_{N,r}+\varepsilon v$ is a rational function of the recurrence entries whose denominators involve only upward coefficients, which are positive at $K_{N,1}$; so $G$ is smooth near $(1,0)$. By Lemma~\ref{lem:corner-value}, $G(r,0)=(1-r)^N$. Put $d=|\dot g|$. On a small rectangle around $(1,0)$, on which the basic sign conditions persist, $\partial_\varepsilon G\leq-d/2$, hence $G(r,\varepsilon)\leq(1-r)^N-d\varepsilon/2<0$ for $\varepsilon\geq4(1-r)^N/d$.
\end{proof}

\begin{corollary}[Optimal order of the stability radius]\label{cor:radius-order}
For $N\geq2$ let $\rho_N(r)$ be the largest $\rho$ such that every array satisfying \eqref{eq:basic} with $\widetilde b_i\geq0$ and with left side of \eqref{eq:closeness} at most $\rho$ has property (P). Then $\rho_N(r)$ is of exact order $(1-r)^N$ as $r\to1$.
\end{corollary}
\begin{proof}
Theorem~\ref{thm:perturbation} gives $\rho_N(r)\geq\eta_N(r)=\tfrac12((1-r)/(32N))^N$ for $r\geq\tfrac12$. For the upper bound, use the terminal direction $\delta c_N=-\operatorname{sgn}(s_N)$, $\delta b_N=\operatorname{sgn}(s_N)$, with all other entries unchanged. By Lemma~\ref{lem:corner} its first-order change is $-|s_N|<0$, and it moves the full array by exactly $\varepsilon$ in the norm of \eqref{eq:closeness}. Put $t=1-r$ and $\varepsilon=Ct^N$ as in Proposition~\ref{prop:thin}. For $N\geq2$ and $r$ near $1$, $\varepsilon\leq t/2$ and $\varepsilon\leq r/2$, so $\widetilde b_N\geq t/2$ and $\widetilde c_N\geq r/2$; every other coefficient is unchanged. The array is admissible for Theorem~\ref{thm:perturbation} and lacks property (P). The restriction $N\geq2$ is needed: every admissible two-point array with $b_1\geq0$ has property (P).
\end{proof}

\paragraph{Computations away from $r=1$.}
The following findings are exact computations, not proofs. They are reproduced by \path{rigidity_probe.py} and \path{smallr_probe.py}. Here $g(N,N;N)$ is computed from column $N$ of the product table, an $O(N^2)$-operation recurrence, so sizes in the hundreds are cheap.
\begin{itemize}
\item For fixed $r\in(\tfrac12,1)$, fixed-size deformations fail at many sizes even though $g(N,N;N)=(1-r)^N$ stays positive at $K_{N,r}$. For the rule $\beta=1$, $\gamma=0$, exact computation shows that property (P) fails at $r=4/5$ (size $1/100$) for every $N$ from $6$ to $14$, and at $r=19/20$ (size $1/1000$) for every $N$ from $4$ to $14$. The signs of the first-order change are not periodic in $N$ in general: at $r=4/5$ they are $+512/1875$ for $N=4$ and $-71936/5859375$ for $N=8$.
\item Below $r=\tfrac12$, the counterexamples we found to shape conditions occur at sizes that grow as $r$ decreases; we did not determine minimal sizes or prove a scaling. For constant-ratio arrays with convex profile, one-kink counterexamples ($m$ unit increments, then $1+\delta$) have $g(N,N;N)<0$ in exact arithmetic at
\begin{center}
\begin{tabular}{@{}lccccccc@{}}
$r$&$2/5$&$1/3$&$3/10$&$1/4$&$2/7$&$1/5$&$1/10$\\
$N$&$20$&$40$&$40$&$60$&$80$&$100$&$500$
\end{tabular}
\end{center}
Concave profiles fail for $N\leq18$ at every tested $r$.
\item Convex profiles with log-concave increments (step ratios nonincreasing and at least $1$) contain Krawtchouk, every geometric profile and the quadratic profiles $x+\kappa x^2$, and they exclude the one-kink counterexamples. Yet $k$ steps of ratio $1+1/(2N)$ followed by flat increments give $g(N,N;N)<0$ at $(r,N,k)=(\tfrac12,80,40)$, $(\tfrac25,32,22)$ and $(\tfrac13,90,62)$ in exact arithmetic. In $80$- and $150$-digit floating-point arithmetic, which agree but are not exact sign certificates, the same happens at $(\tfrac14,250,175)$ and $(\tfrac15,500,400)$.
\end{itemize}
In these searches the convex class failed at every tested $r$ from $1/10$ to $\tfrac12$, the concave class at every tested $r$, and the log-concave convex class at every tested $r$ from $1/5$ to $\tfrac12$ (at $r=1/10$, $N=500$, no failure was found). The deformations that kept $g(N,N;N)$ positive up to $N=200$ were the quadratic profiles $x+\kappa x^2$ and smooth changes of the ratio $c/d$; these are reports of the tested families only.

\section{Open problems}\label{sec:open}

\paragraph{Inequalities beyond geometric increments.}
The geometric criterion imposes exact equalities, whereas the perturbation criterion provides small neighborhoods. Find direct inequalities on successive recurrence coefficients that cover larger nonclassical regions while retaining the full Krawtchouk range. The terminating row and products of degree sum greater than $N$ must remain part of the conclusion.

\paragraph{Sharper stability radii.}
For fixed $N$ and $0<r<1$, determine or estimate the largest coefficient radius for which every admissible stochastic perturbation has property (P). Corollary~\ref{cor:radius-order} shows that the order $(1-r)^N$ as $r\to1$ is optimal; the dependence on $N$, and on $r$ away from $1$, remains open. The bound in Theorem~\ref{thm:perturbation} comes from a single-term lower margin and a worst-case recurrence amplification. Both estimates discard substantial information. A useful improvement would retain a transparent coefficient test and describe its dependence on both $N$ and the bias parameter.

\paragraph{The symmetric endpoint.}
At $r=1$, the reference margin in Lemma~\ref{lem:margin} vanishes because parity forces many coefficients to be zero. Symmetric perturbations preserve the parity zeros, and Theorem~\ref{thm:symmetric} exploits this for Szwarc's quadratic system when $p_0<1/2$. At $p_0=1/2$, and for the symmetric Krawtchouk array, further coefficients on the parity support vanish. Determine perturbation directions and structural constraints that preserve positivity there; continuity alone does not control coefficients emerging from those zeros. For each $N\leq10$ the admissible first-order directions form a cone with nonempty interior, but Theorem~\ref{thm:uniform} and Corollary~\ref{cor:analytic-rules} show that polynomial and analytic uniform rules must satisfy two equalities. A description of the cone for all $N$ is open.

\paragraph{Monotonicity-type criteria for finite systems.}
Szwarc's Theorems~3.2 and~3.3 in~\cite{szwarc} are open conditions of monotonicity type for infinite systems. For finite systems, property (P) at the boundary point is the hypergroup property of the corresponding birth--death chain, and Miclo~\cite[Theorem~31 and Proposition~6]{miclo2015} adapts the wave-equation argument of Bakry and Huet to give inequality conditions for chains that are symmetric under $n\mapsto N-n$ and sufficiently convex. Those conditions exclude the Krawtchouk recurrence and the system \eqref{eq:szwarc-q}. By Theorem~\ref{thm:decomp}, any criterion of this kind for nonsymmetric finite systems, valid including the terminal indices, immediately gives one for symmetric finite systems. Theorem~\ref{thm:low} supplies such hypotheses for all triples except those whose pairwise sums all exceed $N$; the remaining task is to control these deep triples by inequalities that contain the geometric criterion. Convexity of the profile does not suffice even with a constant ratio and $r$ bounded away from $1$: for $d$ with increments $1$ at the first seven steps and $6/5$ at the remaining seven ($N=14$), exact arithmetic gives $g(14,14;14)<0$ at $r=1/2$, and the analogous profile with $N=20$, twelve unit increments and $21/20$ afterwards gives $g(20,20;20)<0$ at $r=2/5$. Log-convex increments fail as well: fourteen unit increments followed by $(21/20)^t$, $t=1,\ldots,4$, give $g(18,18;18)<0$ at $r=1/2$. The admissible bias for such profiles therefore shrinks with $N$, and the terminal product is where positivity fails. Section~\ref{sec:limits} explains part of this: near $r=1$, polynomial and analytic uniform deformations that keep property (P) must satisfy two first-order equalities, and below $r=\tfrac12$ the convex, concave and log-concave convex shape classes have counterexamples at the sizes listed there. Two questions remain. First, prove or refute that admissible fixed-size deformations become exponentially thin in $N$ for fixed $r\in(\tfrac12,1)$. Second, decide whether any inequality criterion covers a range $0<r\leq r_0$ for all $N$. Szwarc-type certificates do not resolve the deep triples either. For each Krawtchouk array tested ($N\leq8$, $r\in\{1,1/2,1/5\}$) every deep coefficient is a nonnegative combination of non-deep coefficients through the relations $Hu=0$ on a backward cone, but the weights must depend on the coefficients: no single weight serves $r=1/5$ and $r=1/2$, so no family of linear inequalities obtained this way contains the Krawtchouk range. Checkerboard-supported weights fail for every tested $r<1$, and the canonical weight solving $H^*v=0$ on the deep region has negative boundary flux. On random perturbed arrays the existence of such certificates coincided with property (P).

\paragraph{Other finite families.}
Find analogous coefficient regions around other finite orthogonal systems and compare their geometry with the Krawtchouk neighborhoods. An algebra with a positive basis may supply the reference margin, but a recurrence criterion must express the resulting admissible deformations without requiring the unknown product coefficients as input.

\section*{AI-use disclosure}

OpenAI Codex was used to develop the proof arguments, search and check source passages, construct exact-arithmetic diagnostics, draft and revise this manuscript, and prepare the Lean translation. Separate AI-assisted reviews checked the algebraic proof, boundary cases, normalizations, and quantitative estimates; these reviews are not human peer review. Anthropic Claude was used to analyse Szwarc's Problem~2 against the survey text, to explore discrete hyperbolic certificates numerically, and to develop and draft Sections~\ref{sec:szwarc} and~\ref{sec:limits} together with their exact diagnostics; these sections have not been independently reviewed. The author set the research objective and retains responsibility for publication decisions and the final mathematical claims. No independent human verification is asserted here. Statements about machine verification refer only to the specific compiled Lean declarations and their documented dependencies, not to the presence of a Lean project or to numerical agreement.

\section*{Code and formalization}

The companion source tree contains \path{probe.py} and \path{verify.py}. The command
\begin{quote}\verb|python3 -u verify.py --max-n 7|\end{quote}
compares recurrence-matrix multiplication with direct multiplication modulo the terminal polynomial on exact rational inputs, checks the perturbation lower bounds, and replays two rejected coefficient-profile tests. It also checks Theorem~\ref{thm:szwarc}, the margin of Lemma~\ref{lem:qmargin} and the negative coefficient for $p_0>1/2$ on exact Szwarc arrays, the identities of Lemma~\ref{lem:qthree} in the graded model, and the lower bound of Theorem~\ref{thm:symmetric} on rational symmetric perturbations. These computations are diagnostics and do not replace the proofs at arbitrary size. For Section~\ref{sec:limits}, \path{rigidity_probe.py} checks Lemma~\ref{lem:corner} exactly for $N\leq20$, the predicted failures of Theorem~\ref{thm:uniform}, the boundary layers of Proposition~\ref{prop:families}, the region of Lemma~\ref{lem:nr} and the fixed-$r$ computations, and \path{smallr_probe.py} replays the small-$r$ counterexamples.

The Lean development formalizes the two main criteria as follows:
\begin{center}
\begin{tabular}{@{}p{0.36\linewidth}p{0.59\linewidth}@{}}
Paper result & Lean declaration\\[3pt]
Theorem~\ref{thm:criterion}: geometric criterion & \path{Szkraw.geometric_criterion}\\[3pt]
Theorem~\ref{thm:perturbation}: perturbation & \path{Szkraw.perturbation_criterion}
\end{tabular}
\end{center}
The first includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The second includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. Both have compiled proofs without added axioms or admitted goals. The results of Section~\ref{sec:szwarc} have not been formalized.

The companion code is available at \url{https://github.com/skypher/szkraw}; the fixed revision cited in~\cite{code} identifies the reviewed proof and audit code. Run \verb|make lean| to build the development and \verb|make axioms| to build and audit the principal statements. The latter invokes \path{lean/CheckAxioms.lean}, which rejects dependencies outside \path{propext}, \path{Classical.choice}, and \path{Quot.sound} and tests rejection of unexpected axioms. The toolchain and dependencies are pinned in \path{lean/lean-toolchain} and \path{lean/lake-manifest.json}. The declaration-by-declaration correspondence, auxiliary formalization coverage, and verification commands are recorded in \path{RESEARCH.md} at that revision. Historical attribution and the open problems are prose claims, not machine-verified statements.

\begin{thebibliography}{9}
\bibitem{askey} R. Askey, \emph{Three notes on orthogonal polynomials}, Stichting Mathematisch Centrum, Afdeling Toegepaste Wiskunde, report TW~114/69, Amsterdam, October 1969; Part~II: \emph{Linearization of the product of orthogonal polynomials II}, \url{https://ir.cwi.nl/pub/7741}.
\bibitem{eagleson} G. K. Eagleson, \emph{A characterization theorem for positive definite sequences on the Krawtchouk polynomials}, Australian Journal of Statistics \textbf{11} (1969), no.~1, 29--38, \href{https://doi.org/10.1111/j.1467-842X.1969.tb00004.x}{\nolinkurl{doi:10.1111/j.1467-842X.1969.tb00004.x}}.
\bibitem{koelink} H. T. Koelink, \emph{$q$-Krawtchouk polynomials as spherical functions on the Hecke algebra of type B}, Transactions of the American Mathematical Society \textbf{352} (2000), no.~10, 4789--4813, \href{https://doi.org/10.1090/S0002-9947-00-02588-5}{\nolinkurl{doi:10.1090/S0002-9947-00-02588-5}}; preprint arXiv:q-alg/9605040v1 (1996), \url{https://arxiv.org/abs/q-alg/9605040v1}. Theorem and equation locators refer to the preprint.
\bibitem{miclo} L. Miclo, \emph{On the hypergroup property}, Annales de la Facult\'e des Sciences de Toulouse, s\'erie~6, \textbf{26} (2017), no.~2, 417--435, \href{https://doi.org/10.5802/afst.1539}{\nolinkurl{doi:10.5802/afst.1539}}.
\bibitem{miclo2015} L. Miclo, \emph{On the Markov commutator}, preprint arXiv:1505.02540 (2015), \url{https://arxiv.org/abs/1505.02540}.
\bibitem{szwarc} R. Szwarc, \emph{Orthogonal polynomials and Banach algebras}, in \emph{Inzell Lectures on Orthogonal Polynomials}, W. zu Castell, F. Filbir, and B. Forster (eds.), Advances in the Theory of Special Functions and Orthogonal Polynomials, vol.~2, Nova Science Publishers, 2005, 103--139; \S5, Problem~2. Author version (2004, 97--133; Problem~2 on printed p.~125): \url{https://www.math.uni.wroc.pl/~szwarc/pdf/inzell.pdf}.
\bibitem{szwarc2003} R. Szwarc, \emph{A necessary and sufficient condition for nonnegative product linearization of orthogonal polynomials}, Constructive Approximation \textbf{19} (2003), 565--573, \href{https://doi.org/10.1007/s00365-002-0524-z}{\nolinkurl{doi:10.1007/s00365-002-0524-z}}.
\bibitem{code} L. P. Polzer, \emph{Companion code for Coefficient criteria for finite nonnegative linearization} (2026), revision \texttt{e65b421} (full identifier in the URL), \url{https://github.com/skypher/szkraw/tree/e65b421f25cec90c8d4097363da80386592ce5ed}.
\end{thebibliography}
\end{document}
```
