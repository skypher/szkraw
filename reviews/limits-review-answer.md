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

