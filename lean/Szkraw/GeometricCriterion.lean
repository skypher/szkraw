import Szkraw.Geometric
import Szkraw.FiniteRealization

namespace Szkraw

/-- The full geometric recurrence criterion, including its finite spectral realization. -/
theorem geometric_criterion : Stmt_geometric := by
  intro N v hv hg
  exact ⟨finite_realization v hv, geometric_matrix_positivity N v hv hg⟩

end Szkraw
