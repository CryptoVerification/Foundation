import Foundation.Resource.PolynomialExecution
import Foundation.Examples.FiniteProgram
import Foundation.Examples.ExecutionCost

namespace Foundation.Examples.PolynomialExecution

open Foundation.Examples.UniformAdversary
  (goal family model constantZero_not_realizable uniform_secure)
open Foundation.Examples.FiniteProgram
  (description)
open Foundation.Examples.ExecutionCost
  (toyCost)

universe u v w

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (D : M.FiniteDescription) {E : M.ExecutionSemantics}
    (C : E.ExecutionCost.{u, v, w}) (F : InstanceFamily P)
    (A : AdversaryFamily P F) :
    (M.polynomialExecutionClass D C).admissible F A ↔
      ∃ prog : M.Program F,
        M.realize F prog = A ∧ PolynomiallyBounded (C.runtime F prog) := by
  rfl

/-- Program `3` is the single realization and polynomial trace-length
witness; `description` separately gives that same program a finite code. -/
example : (model.polynomialExecutionClass description toyCost).admissible
    family (model.realize family (3 : Nat)) := by
  refine ⟨(3 : Nat), rfl, ?_⟩
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.const 3) PolynomiallyBounded.id

example : ¬ (model.polynomialExecutionClass description toyCost).admissible
    family (fun _ => (0 : Nat)) := by
  rintro ⟨prog, hRealize, _⟩
  exact constantZero_not_realizable ⟨prog, hRealize⟩

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (D : M.FiniteDescription) {E : M.ExecutionSemantics}
    (C : E.ExecutionCost.{u, v, w}) (F : InstanceFamily P)
    (A : AdversaryFamily P F)
    (h : (M.polynomialExecutionClass D C).admissible F A) :
    M.uniformClass.admissible F A := by
  rcases h with ⟨prog, hRealize, _⟩
  exact ⟨prog, hRealize⟩

example : SecureOnWithin goal
    (model.polynomialExecutionClass description toyCost) family := by
  apply SecureOnWithin.monoClass
    (C := model.uniformClass)
    (D := model.polynomialExecutionClass description toyCost)
    (F := family) ?_ uniform_secure
  intro F A hA
  rcases hA with ⟨prog, hRealize, _⟩
  exact ⟨prog, hRealize⟩

end Foundation.Examples.PolynomialExecution
