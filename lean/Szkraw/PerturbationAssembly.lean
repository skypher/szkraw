import Szkraw.PerturbationError
import Szkraw.Bandwidth

namespace Szkraw

/-- The paper's single-positive-term lemma, supplied by kraw_triangle_margin. -/
def Stmt_kraw_triangle_margin : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (r : ℝ), 0 < r → r < 1 →
    ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N → Triangle m n.val k.val →
      (min r (1-r)/4)^N ≤ productMatrix (krawCoefficients N r) m n k

/-- Composition with a reference-margin proof. The unconditional application is
perturbation_criterion in KrawtchoukMargin.lean. -/
theorem perturbation_assembly (hmargin : Stmt_kraw_triangle_margin) : Stmt_perturbation := by
  intro N v r hv hr hr1 hclose
  have hs : 0 ≤ min r (1-r) := le_min (le_of_lt hr) (by linarith)
  have hp : 0 ≤ (1/2 : ℝ)*(min r (1-r)/4)^N := by positivity
  have htri : ∀ (m : ℕ) (n k : Fin (N+1)), m ≤ N → Triangle m n.val k.val →
      (1/2 : ℝ)*(min r (1-r)/4)^N ≤ productMatrix v m n k := by
    intro m n k hm ht
    have href := hmargin N hv.1 r hr hr1 m n k hm ht
    have he := (abs_le.mp (perturbation_entry_error v hv r hr hr1 hclose m hm n k)).1
    linarith
  refine ⟨finite_realization v hv,?_,?_⟩
  · intro m hm n k
    by_cases ht : Triangle m n.val k.val
    · exact hp.trans (htri m n k hm ht)
    · rw [product_triangle_zero v hv m hm n k ht]
  · intro m n k hm
    exact ⟨htri m n k hm,product_triangle_zero v hv m hm n k⟩

end Szkraw
