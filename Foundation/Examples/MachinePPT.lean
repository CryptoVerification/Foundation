import Foundation.Machine.PPT
import Foundation.Examples.MachineAdversary
import Foundation.Examples.MachinePolynomialTime
import Foundation.Security.Asymptotic

namespace Machine.Examples

/-- The fixed random-bit code is one witness at every security parameter.
Its complete protocol input has length `n + 3`. -/
theorem randomOutputBit_ppt :
    bitInterface.pptClass.admissible bitFamily
      (bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 2)) := by
  refine ⟨randomOutputBit, (fun _ => 2), bitInputSize,
    PolynomiallyBounded.const 2, randomOutputBit_haltsWithin_any,
    ?_, rfl⟩
  exact PolynomiallyBounded.add PolynomiallyBounded.id
    (PolynomiallyBounded.const 3)

/-- Changing a valid analysis budget does not change the realized family. -/
example :
    bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 2) =
      bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 5) := by
  apply bitInterface.realizeFamily_budget_eq_of_halts
  · exact randomOutputBit_haltsWithin_any
  · intro input
    exact (randomOutputBit_haltsWithin_any input).mono (by omega)

example : bitInterface.uniformModel.uniformClass.admissible bitFamily
    (bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 2)) :=
  bitInterface.pptClass_admissible_uniform randomOutputBit_ppt

example : bitInterface.uniformModel.FiniteDescription :=
  bitInterface.uniformModel_finiteDescription

example : ∃ (p : Machine.Program) (b : Nat → Nat),
    PolynomiallyBounded b ∧
    ∀ n (request : bitInterface.Request n (bitFamily n)),
      HaltsWithin p (bitInterface.machineInput n (bitFamily n) request) (b n) :=
  bitInterface.pptClass_haltsWithin_securityPolynomial randomOutputBit_ppt

example : SecureOnWithin bitGoal bitInterface.pptClass bitFamily := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

end Machine.Examples
