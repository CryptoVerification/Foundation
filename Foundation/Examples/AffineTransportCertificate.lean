import Foundation.Crypto.Logic.Polygraph.AffineTransportCertificate

/-! Executable diagnosis for private-mask correspondence diagrams. These
examples concern the validity of chosen proof witnesses; they do not infer
an attack advantage from an internal inconsistency. -/
namespace CryptoLogic.Polygraph.AffineTransportCertificate.Examples

set_option maxRecDepth 4096

open Foundation.Probability MaskedTransport RootedTransport
open scoped ENNReal

/-- The residual between two retained-state rewrites of the same XOR mask.
The repeated coordinates cancel, even though the syntax is different. -/
def cancelled : Affine 128 :=
  .add (.add (.input 0) (.input 1)) (.add (.input 1) (.input 0))

/-- One missing XOR operand leaves the first secret coordinate in the
residual. Every individual edge still has its exact uniform output law. -/
def missingOperand : Affine 128 := .add (.input 0) (.add (.input 1) (.input 1))

theorem cancelled_check : cancelled.counterexample = none := by decide

theorem cancelled_joint :
    ∃ joint : PMF (Model.Assignment (State := State (Assignment 128))),
      (∀ vertex, joint.map (fun a => a vertex) = law vertex) ∧
      ∀ a ∈ joint.support, (model cancelled.eval).Compatible a :=
  cancelled.diagnosis_correct.mp cancelled_check

theorem missing_counterexample :
    missingOperand.counterexample = some (Affine.basis (0 : Fin 128)) := by decide

theorem missing_obstruction :
    (model missingOperand.eval).Bad (Affine.basis (0 : Fin 128), 0) :=
  missingOperand.obstruction_certificate _ missing_counterexample

theorem cancelled_visits : (cancelled.searchCount (Affine.probes 128)).2 = 903 := by decide
theorem missing_visits : (missingOperand.searchCount (Affine.probes 128)).2 = 10 := by decide

/-- Multiplication is intentionally outside the supported affine syntax.
It vanishes on zero and both basis vectors but not on their sum. -/
def nonlinear : Formula 2 := .mul (.input 0) (.input 1)

theorem nonlinear_fools_basis :
    ∀ state ∈ Affine.probes 2, nonlinear.eval state = 0 := by decide

theorem nonlinear_not_valid : ¬∀ state, nonlinear.eval state = 0 := by
  intro valid
  have h := valid (fun _ => 1)
  norm_num [nonlinear, Formula.eval] at h

theorem nonlinear_count : nonlinear.satisfyingCount = 1 := by decide

/-- This value is both achieved and unavoidable by the general optimum
theorem. Small graph size alone does not make its payload an affine one. -/
theorem nonlinear_obstruction_probability :
    eventProb (model nonlinear.eval).joint (fun a => ¬(model nonlinear.eval).Compatible a) = 1 / 4 := by
  rw [Formula.obstruction_count, nonlinear_count]
  norm_num

theorem nonlinear_unavoidable (candidate : PMF (Model.Assignment (State := State (Assignment 2))))
    (marginals : ∀ vertex, candidate.map (fun a => a vertex) = law vertex) :
    1 / 4 ≤ eventProb candidate (fun a => ¬(model nonlinear.eval).Compatible a) := by
  rw [← nonlinear_obstruction_probability, (model nonlinear.eval).joint_failure]
  exact (model nonlinear.eval).failure_lower_bound candidate (marginals .root)

/-- info: (true, 903, some [1, 0], 10, 1) -/
#guard_msgs in
#eval (cancelled.counterexample.isNone,
  (cancelled.searchCount (Affine.probes 128)).2,
  missingOperand.counterexample.map (fun state => [state 0 |>.val, state 1 |>.val]),
  (missingOperand.searchCount (Affine.probes 128)).2,
  nonlinear.satisfyingCount)

end CryptoLogic.Polygraph.AffineTransportCertificate.Examples
