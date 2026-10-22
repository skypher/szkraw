import Szkraw
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
/-- Enforce the dependency policy, including dependencies of dependencies. -/
elab "assert_allowed_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "unexpected axiom: {ax}"
  logInfo m!"{name}: allowed axioms {axioms}"

-- Regression: a dependency through a theorem must still be rejected.
namespace AxiomAuditRegression
axiom unwanted : False
theorem indirect : False := unwanted
/-- error: unexpected axiom: AxiomAuditRegression.unwanted -/
#guard_msgs in
assert_allowed_axioms indirect
-- Exercise the built-in admitted-proof axiom without an admitted theorem.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admittedDependency : False := sorryAx False true
/-- error: unexpected axiom: sorryAx -/
#guard_msgs in
assert_allowed_axioms admittedDependency
end AxiomAuditRegression

example : Szkraw.Stmt_geometric_matrix := Szkraw.geometric_matrix_positivity
example : Szkraw.Stmt_error_amplification := Szkraw.error_amplification
example : Szkraw.Stmt_geometric := Szkraw.geometric_criterion
example : Szkraw.Stmt_perturbation := Szkraw.perturbation_criterion
example : Szkraw.Stmt_kraw_triangle_margin := Szkraw.kraw_triangle_margin
example : Szkraw.Stmt_logconcave_matrix := Szkraw.logconcave_matrix
example : Szkraw.Stmt_logconcave := Szkraw.logconcave_criterion
example : Szkraw.Stmt_all_products := Szkraw.all_products
example : Szkraw.Stmt_heavy_top := Szkraw.heavy_top
example : Szkraw.Stmt_low_products := Szkraw.low_products
example : Szkraw.Stmt_convex_low := Szkraw.convex_low

assert_allowed_axioms Szkraw.geometric_matrix_positivity
assert_allowed_axioms Szkraw.error_amplification
assert_allowed_axioms Szkraw.elementary_three_term
assert_allowed_axioms Szkraw.tower_mul_nonneg
assert_allowed_axioms Szkraw.spectral_weight_pos
assert_allowed_axioms Szkraw.finite_realization
assert_allowed_axioms Szkraw.geometric_criterion
assert_allowed_axioms Szkraw.product_triangle_zero
assert_allowed_axioms Szkraw.product_difference_recurrence
assert_allowed_axioms Szkraw.matrix_error_amplification
assert_allowed_axioms Szkraw.perturbation_entry_error
assert_allowed_axioms Szkraw.perturbation_assembly
assert_allowed_axioms Szkraw.kraw_triangle_margin
assert_allowed_axioms Szkraw.perturbation_criterion
assert_allowed_axioms Szkraw.squarefree_basis_apply
assert_allowed_axioms Szkraw.squarefree_product_nonneg
assert_allowed_axioms Szkraw.squarefree_trace_diagonal
assert_allowed_axioms Szkraw.tower_trace_square_pos
assert_allowed_axioms Szkraw.tower_trace_self_adjoint
assert_allowed_axioms Szkraw.tower_character_generator
assert_allowed_axioms Szkraw.tower_character_elementary
assert_allowed_axioms Szkraw.tower_character_normalized
assert_allowed_axioms Szkraw.character_normalizer_ratio
assert_allowed_axioms Szkraw.geometric_family_hypotheses
assert_allowed_axioms Szkraw.additional_geometric_class
assert_allowed_axioms Szkraw.nongeometric_perturbation_example
assert_allowed_axioms Szkraw.cube_average_trace
assert_allowed_axioms Szkraw.cube_average_binomial
assert_allowed_axioms Szkraw.binomial_orthogonal
assert_allowed_axioms Szkraw.binomial_norm_pos
assert_allowed_axioms Szkraw.binomial_mass_sum
assert_allowed_axioms Szkraw.binomial_nodes_injective
assert_allowed_axioms Szkraw.binomial_product_identity
assert_allowed_axioms Szkraw.full_krawtchouk_binomial_range
assert_allowed_axioms Szkraw.relatively_open_coefficient_neighborhood
assert_allowed_axioms Szkraw.elementary_products
assert_allowed_axioms Szkraw.logconcave_matrix
assert_allowed_axioms Szkraw.logconcave_criterion
assert_allowed_axioms Szkraw.product_symm
assert_allowed_axioms Szkraw.all_products
assert_allowed_axioms Szkraw.heavy_top
assert_allowed_axioms Szkraw.low_products
assert_allowed_axioms Szkraw.convex_low
assert_allowed_axioms Szkraw.geometric_convex
assert_allowed_axioms Szkraw.piW_entry
