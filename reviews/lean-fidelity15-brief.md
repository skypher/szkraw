# Independent review, Lean fidelity round 15: the lemmas and corollaries of Sections 2–6

As in rounds 1–14, **do not check proofs**. Check only whether each Lean statement faithfully expresses the paper statement, under the acceptance rule: Lean hypotheses equivalent to or weaker than the paper's, Lean conclusion equivalent to or stronger. Where a Lean statement covers less than the paper claim, say so and check that the paper's scope sentences disclose it. Also check that the new table rows and scope sentences describe the Lean declarations accurately.

New since round 14: the Lean table now lists, besides Theorems 2.1 and 5.3 (accepted in earlier rounds), the lemmas and corollaries of Sections 2–6 (Lemma 2.2, Lemmas 3.1–3.3, Proposition 3.4, Lemma 4.1, Lemmas 5.1–5.2, Corollaries 5.4, 6.1, 6.2). These declarations already existed as steps of the proofs of Theorems 2.1 and 5.3; two small declarations are new (`geometric_coefficients_N_one`, and the conjunct `¬ ∃ β, …` in `nongeometric_perturbation_example`). Proposition 6.3 (comparison with Koelink's construction) is declared unformalized.

Conventions (unchanged from earlier rounds):
- `Coefficients N` has fields a, b, c : ℕ → ℝ.
- `Admissible v` is the paper's (2.1): `1 ≤ N ∧ a 0 = 1 ∧ b 0 = 0 ∧ c 0 = 0 ∧ a N = 0 ∧ (∀ i ≤ N, a i + b i + c i = 1) ∧ (∀ i < N, 0 < a i) ∧ (∀ i, 0 < i → i ≤ N → 0 < c i)`.
- `MatrixPositivity v := ∀ m ≤ N, ∀ i j, 0 ≤ productMatrix v m i j`; `productMatrix v m = R_m(J)` (accepted in earlier rounds as the encoding of g(m,n;k)).
- Mathlib's `QuadraticAlgebra R a b` is R ⊕ R·ω with ω² = a + bω; `x.re`, `x.im` are the two coordinates and `⟨x, y⟩ = x + yω`.

Answer format: a table (paper claim | Lean declaration | MATCH / MATCH, SCOPE NOTED / MISMATCH | reason), exact fixes, and an overall verdict (PASS / PASS WITH MINOR FIXES / FAIL). Be terse.

## Part A. Paper statements

```latex
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

The terminal relation is $(x-b_N)R_N-c_NR_{N-1}=0$ on the orthogonality support. Linearization means equality of functions on this support, rather than an unrestricted polynomial identity when the degree sum exceeds $N$.

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

\begin{lemma}[Coefficient parametrization]\label{lem:parameters}
The hypotheses of Theorem~\ref{thm:criterion} are equivalent to
\begin{equation}\label{eq:parameters}
a_i=\frac{q^i[N-i]_q}{[N]_q},\qquad
b_i=(1-r)\frac{[i]_q}{[N]_q},\qquad
c_i=r\frac{[i]_q}{[N]_q}
\end{equation}
for $q\geq1$, $0<r\leq1$. When $N=1$, one may choose $q=1$.
\end{lemma}

Fix $p\geq1$ and $q\geq1$. Starting with $A_{N+1}=\mathbb R$, form recursively the commutative real algebras
\begin{equation}\label{eq:algebra}
A_j=A_{j+1}[z_j]\big/
\left(z_j^2-\left((q-1)\sum_{l=j+1}^N z_l+p-1\right)z_j-pq^{N-j}\right).
\end{equation}
Write $A=A_1$. For $S\subseteq\{1,\ldots,N\}$ let $z_S=\prod_{j\in S}z_j$, with $z_\varnothing=1$.

\begin{lemma}[Basis and positivity]\label{lem:basis}
The elements $z_S$ form a basis of $A$, and all their multiplication coefficients are nonnegative.
\end{lemma}

\begin{lemma}[Positive associative inner product]\label{lem:trace}
Let $\tau$ extract the coefficient of $z_\varnothing$. Then
\begin{equation}\label{eq:trace}
\tau(z_Sz_T)=\boldsymbol1_{S=T}\,p^{|S|}q^{\sum_{j\in S}(N-j)}.
\end{equation}
Consequently $\langle u,v\rangle=\tau(uv)$ is positive definite, and multiplication by every element of $A$ is self-adjoint.
\end{lemma}

Put $E_k=\sum_{|S|=k}z_S$ for $0\leq k\leq N$, and set $E_{-1}=E_{N+1}=0$.

\begin{lemma}[Three-term multiplication]\label{lem:three}
For $0\leq k\leq N$,
\begin{equation}\label{eq:three}
E_1E_k=[k+1]_qE_{k+1}+(p-1)[k]_qE_k+
pq^{k-1}[N-k+1]_qE_{k-1}.
\end{equation}
The last term is interpreted as zero for $k=0$.
\end{lemma}

\begin{proposition}[Positive subalgebra]\label{prop:subalgebra}
The space $B=\operatorname{span}\{E_0,\ldots,E_N\}$ is the subalgebra generated by $E_1$. Every product $E_mE_n$ has nonnegative coefficients in this basis.
\end{proposition}

\begin{lemma}[Positive normalization]\label{lem:normalization}
Evaluation $z_j\mapsto pq^{N-j}$ defines an algebra character $\epsilon$ of $A$. Put $t_k=\epsilon(E_k)>0$. Then
\begin{equation}\label{eq:ratio}
t_0=1,\quad t_1=p[N]_q,\qquad
\frac{t_{k+1}}{t_k}=pq^k\frac{[N-k]_q}{[k+1]_q}\quad(0\leq k<N).
\end{equation}
\end{lemma}

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

\begin{lemma}[A uniform positive margin in the asymmetric case]\label{lem:margin}
For the Krawtchouk recurrence \eqref{eq:parameters} with $q=1$ and $0<r<1$, put $s=\min(r,1-r)$. Every coefficient in its triangle support obeys
\begin{equation}\label{eq:margin}
g(m,n;k)\geq (s/4)^N\quad\text{if }|m-n|\leq k\leq\min(m+n,N).
\end{equation}
\end{lemma}

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

\begin{corollary}[Finite systems outside the geometric family]\label{cor:nonclassical}
For every $N\geq2$, take the Krawtchouk coefficients at $r=1/2$, and replace only
\[
a_1\longmapsto a_1-h,\qquad b_1\longmapsto b_1+h,
\qquad 0<h\leq\frac14(64N)^{-N}.
\]
These recurrences have nonnegative linearization and do not satisfy the constant-ratio hypothesis of Theorem~\ref{thm:criterion}. More generally, Theorem~\ref{thm:perturbation} admits a relatively open neighborhood of the asymmetric Krawtchouk array in the affine space defined by the row-sum and boundary equalities in \eqref{eq:basic}.
\end{corollary}

\begin{corollary}[Full positive Krawtchouk range]\label{cor:kraw}
For every $N\geq1$ and $0<p_0\leq1/2$, Krawtchouk polynomials orthogonal for binomial weights $\binom Nj p_0^{N-j}(1-p_0)^j$ have nonnegative linearization when normalized at $j=0$.
\end{corollary}

\begin{corollary}[The dual $q$-Krawtchouk case]\label{cor:additional}
For every $N\geq2$, $q>1$, and $0<r\leq1$, the recurrence \eqref{eq:parameters} has nonnegative linearization. In the normalization $R_0=1$, $R_1=x$, it is outside the Krawtchouk recurrence class.
\end{corollary}

\begin{proposition}[Relation to the existing algebraic construction]\label{prop:source}
The quadratic relations \eqref{eq:algebra} are those of Koelink~\cite[Theorem~3.1(ii), equation (3.3)]{koelink}, with $z_j=u(x^j)$ and the same parameters $p,q$. The recurrence in this paper is the normalized recurrence of his Theorem~7.1, with $r=1/p$; its polynomial-in-the-spectral-variable interpretation is the dual $q$-Krawtchouk interpretation described after his Theorem~7.8.
\end{proposition}
```

#### Code-and-formalization: new table rows, scope sentences, disclosure
```latex
Theorem~\ref{thm:criterion}: geometric criterion & \path{Szkraw.geometric_criterion}\\[3pt]
Lemma~\ref{lem:parameters}: coefficient parametrization & \path{Szkraw.geometric_parameters}, \path{Szkraw.geometric_coefficients_admissible}, \path{Szkraw.geometric_family_hypotheses}, \path{Szkraw.geometric_coefficients_N_one}\\[3pt]
Lemma~\ref{lem:basis}: basis and positivity & \path{Szkraw.squarefreeBasis}, \path{Szkraw.squarefree_basis_apply}, \path{Szkraw.squarefree_product_nonneg}\\[3pt]
Lemma~\ref{lem:trace}: positive associative inner product & \path{Szkraw.squarefree_trace_diagonal}, \path{Szkraw.tower_trace_square_pos}, \path{Szkraw.tower_trace_self_adjoint}\\[3pt]
Lemma~\ref{lem:three}: three-term multiplication & \path{Szkraw.elementary_three_term}, \path{Szkraw.elementary_one}\\[3pt]
Proposition~\ref{prop:subalgebra}: positive subalgebra & \path{Szkraw.elementary_products}\\[3pt]
Lemma~\ref{lem:normalization}: positive normalization & \path{Szkraw.towerCharacter}, \path{Szkraw.tower_character_generator}, \path{Szkraw.tower_character_elementary}, \path{Szkraw.normalizer_pos}, \path{Szkraw.normalizer_one}, \path{Szkraw.character_normalizer_ratio}\\[3pt]
Lemma~\ref{lem:finite}: finite realization and triangle support & \path{Szkraw.finite_realization}, \path{Szkraw.product_triangle_zero}\\[3pt]
Lemma~\ref{lem:margin}: uniform positive margin & \path{Szkraw.kraw_triangle_margin}\\[3pt]
Theorem~\ref{thm:perturbation}: perturbation & \path{Szkraw.perturbation_criterion}\\[3pt]
Corollary~\ref{cor:nonclassical}: systems outside the geometric family & \path{Szkraw.nongeometric_perturbation_example}, \path{Szkraw.relatively_open_coefficient_neighborhood}\\[3pt]
Corollary~\ref{cor:kraw}: full positive Krawtchouk range & \path{Szkraw.full_krawtchouk_binomial_range}, \path{Szkraw.binomial_normalized_at_zero}, \path{Szkraw.binomial_node_probability_convention}\\[3pt]
Corollary~\ref{cor:additional}: dual $q$-Krawtchouk case & \path{Szkraw.additional_geometric_class}\\[3pt]

The entry for Theorem~\ref{thm:criterion} includes a positive finite orthogonality measure, distinct support points, the terminal relation, and all finite product identities. The entry for Theorem~\ref{thm:perturbation} includes the explicit radius, positive triangle margin, and exact zeros outside the triangle. In Sections~\ref{sec:algebra} and~\ref{sec:normalization} the algebra $A$ is the iterated quadratic extension \path{Szkraw.tower}, whose generator adjoined at stage $N+1-j$ is $z_j$ with the square relation \eqref{eq:algebra}; subsets $S$ are encoded as $\{0,1\}$-vectors of length $N$, $\tau$ is \path{Szkraw.towerTrace}, $E_k$ is \path{Szkraw.elementary} and $t_k$ is \path{Szkraw.normalizer}. Lemma~\ref{lem:parameters} is stated with $p=1/r\geq1$ in both directions. Lemma~\ref{lem:three} is stated for $k\geq1$; for $k=0$ it reads $E_1=E_1$, where $E_1$ is the sum of the generators (\path{Szkraw.elementary_one}). In Proposition~\ref{prop:subalgebra} Lean states that every product $E_mE_n$ with $m,n\leq N$ is a combination of $E_0,\ldots,E_N$ with nonnegative coefficients; that $B$ is generated by $E_1$ and the independence of the $E_k$ are not stated separately. In Lemma~\ref{lem:normalization} the character is an $\mathbb R$-algebra homomorphism with $z_j\mapsto pq^{N-j}$. In Corollary~\ref{cor:nonclassical} Lean states, for the explicit arrays, \eqref{eq:basic}, the failure of the constant-ratio hypothesis, nonnegative linearization and the margin of Theorem~\ref{thm:perturbation}; for its last sentence it gives, for every $0<r<1$, an open set in the subspace of arrays satisfying the equalities in \eqref{eq:basic} that contains the Krawtchouk array at $r$ and consists of arrays with nonnegative linearization. In Corollary~\ref{cor:kraw} Lean states nonnegative linearization of the array \eqref{eq:parameters} with $q=1$ and $r=p_0/(1-p_0)$, the orthogonality of its polynomials for the binomial weights at the nodes $1-j/(N(1-p_0))$, and their value $1$ at $j=0$; the sharpness remark in its proof is not formalized. In Corollary~\ref{cor:additional}, ``outside the Krawtchouk recurrence class'' is formalized as disagreement of $b_i+c_i$ with the profile of every Krawtchouk array. Proposition~\ref{prop:source} is a comparison with the literature and is not formalized.

``Machine-verified'' refers only to the Lean theorems listed in the section on code and formalization, with the axioms stated there. Results and prose remarks not covered by those listed Lean theorems are supported by written proofs, AI review and exact numerical checks, but are not machine-verified.
```

## Part B. Lean statements

### Definitions: the algebra tower, squarefree monomials, elementary sums, trace, character
```lean
-- Szkraw/QuadraticTower.lean
structure AlgebraStage where
  Carrier : Type
  [ring : CommRing Carrier]
  [algebra : Algebra ℝ Carrier]
  sum : Carrier

-- Szkraw/QuadraticTower.lean
@[reducible] noncomputable def tower (p q : ℝ) : ℕ → AlgebraStage
  | 0 => { Carrier := ℝ, sum := 0 }
  | n+1 =>
    let T := tower p q n
    { Carrier := QuadraticAlgebra T.Carrier (algebraMap ℝ T.Carrier (p*q^n))
        ((q-1) • T.sum + algebraMap ℝ T.Carrier (p-1))
      sum := ⟨T.sum, 1⟩ }

-- Szkraw/TowerTrace.lean
noncomputable def squarefree (p q : ℝ) : (N : ℕ) → (Fin N → Bool) → (tower p q N).Carrier
  | 0, _ => 1
  | N+1, b => if b 0 then ⟨0,squarefree p q N (Fin.tail b)⟩
    else ⟨squarefree p q N (Fin.tail b),0⟩

-- Szkraw/TowerTrace.lean
noncomputable def towerTrace (p q : ℝ) : (N : ℕ) → (tower p q N).Carrier → ℝ
  | 0, x => x
  | N+1, x => towerTrace p q N x.re

-- Szkraw/Elementary.lean
def bitsWeight : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, b => (if b 0 then 1 else 0) + bitsWeight n (Fin.tail b)

-- Szkraw/TowerTrace.lean
def bitsExponent : (N : ℕ) → (Fin N → Bool) → ℕ
  | 0, _ => 0
  | N+1, b => (if b 0 then N else 0)+bitsExponent N (Fin.tail b)

-- Szkraw/Elementary.lean
def qInteger (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => qInteger q n + q^n

-- Szkraw/Elementary.lean
noncomputable def elementary (p q : ℝ) : (n : ℕ) → ℕ → (tower p q n).Carrier
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => ⟨elementary p q n (k+1), elementary p q n k⟩

-- Szkraw/Normalization.lean
noncomputable def normalizer (p q : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => normalizer p q N k * (p*q^k*qInteger q (N-k)/qInteger q (k+1))

-- Szkraw/Normalization.lean
noncomputable def normalizedElementary (p q : ℝ) (N k : ℕ) : (tower p q N).Carrier :=
  (normalizer p q N k)⁻¹ • elementary p q N k

-- Szkraw/TowerCharacter.lean
noncomputable def towerEval (p q : ℝ) : (N : ℕ) → (tower p q N).Carrier → ℝ
  | 0, x => x
  | N+1, x => towerEval p q N x.re + p*q^N*towerEval p q N x.im

-- Szkraw/TowerCharacter.lean
noncomputable def towerCharacter (p q : ℝ) (N : ℕ) : (tower p q N).Carrier →ₐ[ℝ] ℝ where
  toFun := towerEval p q N
  map_one' := tower_eval_one p q N
  map_mul' := tower_eval_mul p q N
  map_zero' := tower_eval_zero p q N
  map_add' := tower_eval_add p q N
  commutes' := fun r => tower_eval_scalar p q r N

-- Szkraw/TowerCharacter.lean
noncomputable def towerGenerator (p q : ℝ) : (N : ℕ) → Fin N → (tower p q N).Carrier
  | 0, i => Fin.elim0 i
  | N+1, i => Fin.cases ⟨0,1⟩ (fun j => ⟨towerGenerator p q N j,0⟩) i

-- Szkraw/SquarefreeBasis.lean
noncomputable def coordinateEquiv (p q : ℝ) (N : ℕ) :
    (tower p q N).Carrier ≃ₗ[ℝ] ((Fin N → Bool) → ℝ) where
  toFun := coordinate p q N
  invFun := fromCoordinates p q N
  left_inv := from_coordinates_coordinate p q N
  right_inv f := funext (coordinate_from_coordinates p q N f)
  map_add' x y := funext (coordinate_add p q N x y)
  map_smul' r x := funext (coordinate_smul p q r N x)

-- Szkraw/SquarefreeBasis.lean
noncomputable def squarefreeBasis (p q : ℝ) (N : ℕ) :
    Module.Basis (Fin N → Bool) ℝ (tower p q N).Carrier :=
  Module.Basis.ofEquivFun (coordinateEquiv p q N)

```

### Lemma 2.2 (lem:parameters)
```lean
-- Szkraw/Parameters.lean
noncomputable def geometricCoefficients (N : ℕ) (p q : ℝ) : Coefficients N where
  a i := q^i*qInteger q (N-i)/qInteger q N
  b i := (p-1)*qInteger q i/(p*qInteger q N)
  c i := qInteger q i/(p*qInteger q N)

-- Szkraw/Parameters.lean
def Stmt_geometric_parameters : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Geometric v →
    ∃ p q : ℝ, 1 ≤ p ∧ 1 ≤ q ∧ ∀ i, i ≤ N →
      v.a i = (geometricCoefficients N p q).a i ∧
      v.b i = (geometricCoefficients N p q).b i ∧
      v.c i = (geometricCoefficients N p q).c i

-- Szkraw/Parameters.lean
theorem geometric_parameters : Stmt_geometric_parameters

-- Szkraw/Parameters.lean
theorem geometric_coefficients_admissible (N : ℕ) (hN : 1 ≤ N)
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Admissible (geometricCoefficients N p q)

-- Szkraw/GeometricApplications.lean
/-- The converse direction of the paper's coefficient-parametrization lemma. -/
theorem geometric_family_hypotheses (N : ℕ) (hN : 1 ≤ N) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) : Geometric (geometricCoefficients N p q)

-- Szkraw/GeometricApplications.lean
/-- For `N = 1` the coefficients `(eq:parameters)` do not depend on `q`, so one may choose `q = 1`. -/
theorem geometric_coefficients_N_one (p q : ℝ) (i : ℕ) (hi : i ≤ 1) :
    (geometricCoefficients 1 p q).a i = (geometricCoefficients 1 p 1).a i ∧
    (geometricCoefficients 1 p q).b i = (geometricCoefficients 1 p 1).b i ∧
    (geometricCoefficients 1 p q).c i = (geometricCoefficients 1 p 1).c i

```

### Lemma 3.1 (lem:basis)
```lean
-- Szkraw/SquarefreeBasis.lean
theorem squarefree_basis_apply (p q : ℝ) (N : ℕ) (b : Fin N → Bool) :
    squarefreeBasis p q N b = squarefree p q N b

-- Szkraw/SquarefreeBasis.lean
theorem squarefree_index_card (N : ℕ) : Fintype.card (Fin N → Bool) = 2^N

-- Szkraw/SquarefreeBasis.lean
theorem squarefree_product_nonneg (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (b c d : Fin N → Bool) :
    0 ≤ (squarefreeBasis p q N).repr (squarefreeBasis p q N b*squarefreeBasis p q N c) d

```

### Lemma 3.2 (lem:trace)
```lean
-- Szkraw/TowerTrace.lean
theorem squarefree_trace_diagonal (p q : ℝ) (N : ℕ) (b c : Fin N → Bool) :
    towerTrace p q N (squarefree p q N b*squarefree p q N c) =
      if b = c then p^(bitsWeight N b)*q^(bitsExponent N b) else 0

-- Szkraw/TowerTrace.lean
theorem tower_trace_square_pos (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) (hx : x ≠ 0) :
    0 < towerTrace p q N (x*x)

-- Szkraw/TowerTrace.lean
theorem tower_trace_square_eq_zero (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (x : (tower p q N).Carrier) : towerTrace p q N (x*x) = 0 ↔ x = 0

-- Szkraw/TowerTrace.lean
theorem tower_trace_self_adjoint (p q : ℝ) (N : ℕ) (h x y : (tower p q N).Carrier) :
    towerTrace p q N ((h*x)*y) = towerTrace p q N (x*(h*y))

```

### Lemma 3.3 (lem:three)
```lean
-- Szkraw/ThreeTerm.lean
def Stmt_elementary_three_term : Prop :=
  ∀ (p q : ℝ) (n k : ℕ),
    (tower p q n).sum * elementary p q n (k+1) =
      qInteger q (k+2) • elementary p q n (k+2) +
      ((p-1)*qInteger q (k+1)) • elementary p q n (k+1) +
      (p*q^k*qInteger q (n-k)) • elementary p q n k

-- Szkraw/ThreeTerm.lean
theorem elementary_three_term : Stmt_elementary_three_term

-- Szkraw/Elementary.lean
theorem elementary_one (p q : ℝ) (n : ℕ) :
    elementary p q n 1 = (tower p q n).sum

-- Szkraw/Elementary.lean
theorem elementary_zero (p q : ℝ) (n : ℕ) : elementary p q n 0 = 1

-- Szkraw/Elementary.lean
theorem elementary_above (p q : ℝ) (n k : ℕ) (h : n < k) :
    elementary p q n k = 0

```

### Proposition 3.4 (prop:subalgebra)
```lean
-- Szkraw/AlgebraProducts.lean
/-- The unnormalized positive product expansion asserted in the paper's subalgebra proposition. -/
theorem elementary_products (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    ∃ g : Fin (N+1) → ℝ, (∀ k, 0 ≤ g k) ∧
      elementary p q N m*elementary p q N n = ∑ k, g k • elementary p q N k.val

```

### Lemma 4.1 (lem:normalization)
```lean
-- Szkraw/TowerCharacter.lean
theorem tower_character_generator (p q : ℝ) (N : ℕ) (i : Fin N) :
    towerCharacter p q N (towerGenerator p q N i) = p*q^(N-1-i.val)

-- Szkraw/TowerCharacter.lean
theorem tower_character_elementary (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    towerCharacter p q N (elementary p q N k) = normalizer p q N k

-- Szkraw/Normalization.lean
theorem normalizer_pos (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k ≤ N) : 0 < normalizer p q N k

-- Szkraw/Normalization.lean
theorem normalizer_one (p q : ℝ) (N : ℕ) : normalizer p q N 1 = p*qInteger q N

-- Szkraw/TowerCharacter.lean
theorem character_normalizer_ratio (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (N k : ℕ) (hk : k < N) :
    normalizer p q N (k+1)/normalizer p q N k =
      p*q^k*qInteger q (N-k)/qInteger q (k+1)

```

### Lemma 5.1 (lem:finite)
```lean
-- Szkraw/Statements.lean
def recurrenceMatrix {N : ℕ} (v : Coefficients N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  if j.val = i.val + 1 then v.a i.val
  else if j = i then v.b i.val
  else if i.val = j.val + 1 then v.c i.val else 0

-- Szkraw/Statements.lean
noncomputable def polynomialPair {N : ℕ} (v : Coefficients N) :
    ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (0, 1)
  | n + 1 => let t := polynomialPair v n
      (t.2, Polynomial.C (v.a n)⁻¹ *
        ((Polynomial.X - Polynomial.C (v.b n)) * t.2 - Polynomial.C (v.c n) * t.1))

-- Szkraw/Statements.lean
noncomputable def recurrencePolynomial {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Polynomial ℝ := (polynomialPair v m).2

-- Szkraw/Statements.lean
noncomputable def matrixPair {N : ℕ} (v : Coefficients N) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ×
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => (0, 1)
  | n + 1 => let t := matrixPair v n
      (t.2, (v.a n)⁻¹ •
        ((recurrenceMatrix v - v.b n • (1 : Matrix _ _ ℝ)) * t.2 - v.c n • t.1))

-- Szkraw/Statements.lean
noncomputable def productMatrix {N : ℕ} (v : Coefficients N) (m : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (matrixPair v m).2

-- Szkraw/Statements.lean
/-- A positive discrete orthogonality measure on exactly N+1 points together
with the terminal relation and matrix-to-polynomial product identity. -/
def FiniteRealization {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ x w : Fin (N+1) → ℝ, Function.Injective x ∧
    (∀ t, 0 < w t) ∧ (∑ t, w t) = 1 ∧
    (∀ m, m ≤ N → (recurrencePolynomial v m).eval 1 = 1) ∧
    (∀ (m : ℕ) (n : Fin (N+1)), m ≤ N →
      ∑ k : Fin (N+1), productMatrix v m n k = 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ t, w t * (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n).eval (x t) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ t, w t * ((recurrencePolynomial v m).eval (x t))^2) ∧
    (∀ t, (x t-v.b N) * (recurrencePolynomial v N).eval (x t) -
      v.c N * (recurrencePolynomial v (N-1)).eval (x t) = 0) ∧
    (∀ (m : ℕ) (n t : Fin (N+1)), m ≤ N →
      (recurrencePolynomial v m).eval (x t) *
        (recurrencePolynomial v n.val).eval (x t) =
      ∑ k : Fin (N+1), productMatrix v m n k *
        (recurrencePolynomial v k.val).eval (x t))

-- Szkraw/FiniteRealization.lean
theorem finite_realization {N : ℕ} (v : Coefficients N) (hv : Admissible v) :
    FiniteRealization v

-- Szkraw/Statements.lean
def Triangle (m n k : ℕ) : Prop := m ≤ n+k ∧ n ≤ m+k ∧ k ≤ m+n

-- Szkraw/Bandwidth.lean
theorem product_triangle_zero {N : ℕ} (v : Coefficients N) (hv : Admissible v)
    (m : ℕ) (hm : m ≤ N) (n k : Fin (N+1)) (h : ¬ Triangle m n.val k.val) :
    productMatrix v m n k = 0

```

### Lemma 5.2 (lem:margin)
```lean
-- Szkraw/Krawtchouk.lean
noncomputable def krawCoefficients (N : ℕ) (r : ℝ) : Coefficients N where
  a i := ((N : ℝ)-i)/N
  b i := (1-r)*i/N
  c i := r*i/N

-- Szkraw/PerturbationAssembly.lean
/-- The paper's single-positive-term lemma, supplied by kraw_triangle_margin. -/
def Stmt_kraw_triangle_margin : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (r : ℝ), 0 < r → r < 1 →
    ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N → Triangle m n.val k.val →
      (min r (1-r)/4)^N ≤ productMatrix (krawCoefficients N r) m n k

-- Szkraw/KrawtchoukMargin.lean
theorem kraw_triangle_margin : Stmt_kraw_triangle_margin

```

### Corollary 5.4 (cor:nonclassical)
```lean
-- Szkraw/Statements.lean
def Geometric {N : ℕ} (v : Coefficients N) : Prop :=
  ∃ β q : ℝ, 0 ≤ β ∧ 1 ≤ q ∧
    (∀ i, 0 < i → i ≤ N → v.b i = β * v.c i) ∧
    (∀ i, 0 < i → i ≤ N → 0 < (v.b i + v.c i) - (v.b (i-1) + v.c (i-1))) ∧
    (∀ i, 0 < i → i < N →
      (v.b (i+1) + v.c (i+1)) - (v.b i + v.c i) =
        q * ((v.b i + v.c i) - (v.b (i-1) + v.c (i-1))))

-- Szkraw/Statements.lean
def PerturbationMargin {N : ℕ} (v : Coefficients N) (r : ℝ) : Prop :=
  ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N →
    (Triangle m n.val k.val →
      (1/2 : ℝ)*(min r (1-r)/4)^N ≤ productMatrix v m n k) ∧
    (¬ Triangle m n.val k.val → productMatrix v m n k = 0)

-- Szkraw/NongeometricExample.lean
noncomputable def singlePerturbation (N : ℕ) (h : ℝ) : Coefficients N where
  a i := (krawCoefficients N (1/2)).a i - if i = 1 then h else 0
  b i := (krawCoefficients N (1/2)).b i + if i = 1 then h else 0
  c i := (krawCoefficients N (1/2)).c i

-- Szkraw/NongeometricExample.lean
/-- The paper's explicit finite examples outside the geometric family. -/
theorem nongeometric_perturbation_example (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 0 < h) (hhb : h ≤ (1/4 : ℝ)*((64*(N : ℝ))⁻¹)^N) :
    Admissible (singlePerturbation N h) ∧ ¬ Geometric (singlePerturbation N h) ∧
    (¬ ∃ β : ℝ, ∀ i, 0 < i → i ≤ N → (singlePerturbation N h).b i = β * (singlePerturbation N h).c i) ∧
    FiniteRealization (singlePerturbation N h) ∧ MatrixPositivity (singlePerturbation N h) ∧
    PerturbationMargin (singlePerturbation N h) (1/2)

-- Szkraw/CoefficientNeighborhood.lean
abbrev FiniteArray (N : ℕ) := Fin 3 → Fin (N+1) → ℝ

-- Szkraw/CoefficientNeighborhood.lean
def AffineConventions {N : ℕ} (A : FiniteArray N) : Prop :=
  A 0 0 = 1 ∧ A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 0 ⟨N,by omega⟩ = 0 ∧
    ∀ i : Fin (N+1), A 0 i+A 1 i+A 2 i = 1

-- Szkraw/CoefficientNeighborhood.lean
noncomputable def referenceArray (N : ℕ) (r : ℝ) : FiniteArray N := fun c i =>
  if c.val = 0 then (krawCoefficients N r).a i.val
  else if c.val = 1 then (krawCoefficients N r).b i.val
  else (krawCoefficients N r).c i.val

-- Szkraw/CoefficientNeighborhood.lean
noncomputable def arrayCoefficients {N : ℕ} (A : FiniteArray N) : Coefficients N where
  a i := if hi : i ≤ N then A 0 ⟨i,by omega⟩ else 0
  b i := if hi : i ≤ N then A 1 ⟨i,by omega⟩ else 0
  c i := if hi : i ≤ N then A 2 ⟨i,by omega⟩ else 0

-- Szkraw/CoefficientNeighborhood.lean
/-- A nonempty open neighborhood in the affine convention subspace, for every asymmetric reference. -/
theorem relatively_open_coefficient_neighborhood (N : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ∃ U : Set {A : FiniteArray N // AffineConventions A}, IsOpen U ∧
      (⟨referenceArray N r,reference_array_affine N hN r hr hr1⟩ : {A : FiniteArray N // AffineConventions A}) ∈ U ∧
      ∀ A ∈ U, FiniteRealization (arrayCoefficients A.val) ∧ MatrixPositivity (arrayCoefficients A.val) ∧
        PerturbationMargin (arrayCoefficients A.val) r

```

### Corollary 6.1 (cor:kraw)
```lean
-- Szkraw/BinomialMeasure.lean
noncomputable def binomialNode (p : ℝ) (N j : ℕ) : ℝ := 1-(p+1)*(j : ℝ)/(p*N)

-- Szkraw/BinomialMeasure.lean
/-- Orthogonality for the explicitly stated binomial weights, throughout the positive range. -/
theorem full_krawtchouk_binomial_range (N : ℕ) (hN : 1 ≤ N) (p₀ : ℝ)
    (hp₀ : 0 < p₀) (hp₀half : p₀ ≤ 1/2) :
    MatrixPositivity (geometricCoefficients N ((1-p₀)/p₀) 1) ∧
    (∀ m n, m ≤ N → n ≤ N → m ≠ n →
      ∑ j : Fin (N+1), (N.choose j.val : ℝ)*p₀^(N-j.val)*(1-p₀)^j.val *
        (recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) m).eval
          (binomialNode ((1-p₀)/p₀) N j.val) *
        (recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) n).eval
          (binomialNode ((1-p₀)/p₀) N j.val) = 0) ∧
    (∀ m, m ≤ N → 0 < ∑ j : Fin (N+1),
      (N.choose j.val : ℝ)*p₀^(N-j.val)*(1-p₀)^j.val *
        ((recurrencePolynomial (geometricCoefficients N ((1-p₀)/p₀) 1) m).eval
          (binomialNode ((1-p₀)/p₀) N j.val))^2)

-- Szkraw/BinomialMeasure.lean
theorem binomial_normalized_at_zero (p : ℝ) (hp : 1 ≤ p) (N : ℕ) (hN : 1 ≤ N)
    (m : ℕ) (hm : m ≤ N) :
    (recurrencePolynomial (geometricCoefficients N p 1) m).eval (binomialNode p N 0) = 1

-- Szkraw/BinomialMeasure.lean
theorem binomial_node_probability_convention (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀half : p₀ ≤ 1/2)
    (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    binomialNode ((1-p₀)/p₀) N j = 1-(j : ℝ)/(N*(1-p₀))

```

### Corollary 6.2 (cor:additional)
```lean
-- Szkraw/GeometricApplications.lean
theorem additional_geometric_class (N : ℕ) (hN : 2 ≤ N) (p q : ℝ)
    (hp : 1 ≤ p) (hq : 1 < q) :
    Admissible (geometricCoefficients N p q) ∧ Geometric (geometricCoefficients N p q) ∧
    FiniteRealization (geometricCoefficients N p q) ∧ MatrixPositivity (geometricCoefficients N p q) ∧
    ¬ ∃ r : ℝ, ∀ i, i ≤ N →
      (geometricCoefficients N p q).b i+(geometricCoefficients N p q).c i =
      (krawCoefficients N r).b i+(krawCoefficients N r).c i

```

