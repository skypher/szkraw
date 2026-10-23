import Szkraw.Kink500
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Axiom audit of the optional target `Szkraw.Kink500` (`make axioms-kink500`), with the same allowlist as
`CheckAxioms.lean`. -/

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

assert_allowed_axioms Szkraw.kink500_chunk1
assert_allowed_axioms Szkraw.kink500_chunk2
assert_allowed_axioms Szkraw.kink500_chunk3
assert_allowed_axioms Szkraw.kink500_chunk4
assert_allowed_axioms Szkraw.kink500_corner
assert_allowed_axioms Szkraw.kink500_1_10_fails
