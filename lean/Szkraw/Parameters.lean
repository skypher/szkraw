import Szkraw.Statements
import Szkraw.Normalization

namespace Szkraw

theorem qInteger_add (q : ℝ) (m n : ℕ) :
    qInteger q (m+n) = qInteger q m + q^m*qInteger q n := by
  induction n with
  | zero => simp [qInteger]
  | succ n ih =>
      rw [Nat.add_succ, qInteger, ih, qInteger, pow_add]
      ring

theorem geometric_profile (N : ℕ) (d : ℕ → ℝ) (q : ℝ) (hN : 1 ≤ N)
    (hq : 1 ≤ q) (h0 : d 0 = 0) (hterm : d N = 1)
    (hrec : ∀ i, 0 < i → i < N → d (i+1)-d i = q*(d i-d (i-1))) :
    ∀ i, i ≤ N → d i = qInteger q i/qInteger q N := by
  have hinc : ∀ k, k+1 ≤ N → d (k+1)-d k = d 1*q^k := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have hr := hrec (k+1) (by omega) (by omega)
      have hi := ih (by omega)
      simp only [Nat.add_sub_cancel] at hr
      rw [hi] at hr
      rw [hr, pow_succ]
      ring
  have hd : ∀ i, i ≤ N → d i = d 1*qInteger q i := by
    intro i
    induction i with
    | zero => intro _; simp [h0, qInteger]
    | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hstep := hinc i hi
        rw [qInteger]
        nlinarith
  have hQN := qInteger_pos q hq N (by omega)
  have hbase : d 1 = 1/qInteger q N := by
    have hh := hd N (le_refl _)
    rw [hterm] at hh
    apply (eq_div_iff (ne_of_gt hQN)).2
    linarith
  intro i hi
  rw [hd i hi, hbase]
  ring

noncomputable def geometricCoefficients (N : ℕ) (p q : ℝ) : Coefficients N where
  a i := q^i*qInteger q (N-i)/qInteger q N
  b i := (p-1)*qInteger q i/(p*qInteger q N)
  c i := qInteger q i/(p*qInteger q N)

theorem geometric_coefficients_admissible (N : ℕ) (hN : 1 ≤ N)
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Admissible (geometricCoefficients N p q) := by
  have hp0 : 0 < p := by linarith
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [geometricCoefficients, qInteger, ne_of_gt hQN]
  · simp [geometricCoefficients, qInteger]
  · simp [geometricCoefficients, qInteger]
  · simp [geometricCoefficients, qInteger]
  · intro i hi
    have hs := qInteger_add q i (N-i)
    have he : i+(N-i) = N := by omega
    rw [he] at hs
    dsimp [geometricCoefficients]
    field_simp [ne_of_gt hp0, ne_of_gt hQN]
    nlinarith [congrArg (fun t : ℝ => p*t) hs]
  · intro i hi
    exact div_pos (mul_pos (pow_pos (by linarith) _)
      (qInteger_pos q hq (N-i) (by omega))) hQN
  · intro i hi _
    exact div_pos (qInteger_pos q hq i hi) (mul_pos hp0 hQN)

def Stmt_geometric_parameters : Prop :=
  ∀ (N : ℕ) (v : Coefficients N), Admissible v → Geometric v →
    ∃ p q : ℝ, 1 ≤ p ∧ 1 ≤ q ∧ ∀ i, i ≤ N →
      v.a i = (geometricCoefficients N p q).a i ∧
      v.b i = (geometricCoefficients N p q).b i ∧
      v.c i = (geometricCoefficients N p q).c i

theorem geometric_parameters : Stmt_geometric_parameters := by
  intro N v hv hg
  rcases hv with ⟨hN,ha0,hb0,hc0,haN,hsum,hapos,hcpos⟩
  rcases hg with ⟨β,q,hβ,hq,hratio,hinc,hrec⟩
  let p : ℝ := 1+β
  have hp : 1 ≤ p := by dsimp [p]; linarith
  have hp0 : 0 < p := by linarith
  have hQN : 0 < qInteger q N := qInteger_pos q hq N (by omega)
  have hd0 : v.b 0+v.c 0 = 0 := by rw [hb0,hc0]; ring
  have hdN : v.b N+v.c N = 1 := by have := hsum N (le_refl _); linarith
  have hd := geometric_profile N (fun i => v.b i+v.c i) q hN hq hd0 hdN hrec
  refine ⟨p,q,hp,hq,?_⟩
  intro i hi
  have hrat : v.b i = β*v.c i := by
    by_cases h : i = 0
    · subst i; rw [hb0,hc0]; ring
    · exact hratio i (by omega) hi
  have hprof := hd i hi
  have hc : v.c i = qInteger q i/(p*qInteger q N) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hp0 hQN))).2
    apply (eq_div_iff (ne_of_gt hQN)).mp at hprof
    dsimp [p]
    rw [hrat] at hprof
    nlinarith
  have hb : v.b i = (p-1)*qInteger q i/(p*qInteger q N) := by
    rw [hrat,hc]
    dsimp [p]
    ring
  have ha : v.a i = q^i*qInteger q (N-i)/qInteger q N := by
    have hsplit := qInteger_add q i (N-i)
    have hindex : i+(N-i) = N := by omega
    rw [hindex] at hsplit
    have hvs := hsum i hi
    apply (eq_div_iff (ne_of_gt hQN)).2
    apply (eq_div_iff (ne_of_gt hQN)).mp at hprof
    nlinarith
  exact ⟨ha,hb,hc⟩

example : Stmt_geometric_parameters := geometric_parameters

end Szkraw
