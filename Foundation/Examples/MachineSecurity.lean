import Foundation.Crypto.Semantics.Machine.Security
import Foundation.Examples.MachineProgramTransformation

namespace Machine.Examples

/-- Identity transport uses the identity finite-code compiler. -/
example (hTarget : SecureOnWithin bitGoal bitInterface.pptClass bitFamily) :
    SecureOnWithin bitGoal bitInterface.pptClass bitFamily := by
  exact (Reduction.id bitGoal).secureOnWithin_machinePPT
    bitInterface bitInterface bitFamily
    (Reduction.MachineProgramTransformation.id bitInterface)
    AdvantageBound.id_preservesNegligible hTarget

/-- One-step transport uses the finite-code transformation certificate. -/
example (hTarget : SecureOnWithin bitGoal bitInterface.pptClass
    (constantAnswerReduction.mapFamily bitFamily)) :
    SecureOnWithin bitGoal bitInterface.pptClass bitFamily := by
  exact constantAnswerReduction.secureOnWithin_machinePPT
    bitInterface bitInterface bitFamily constantAnswerTransformation
    AdvantageBound.id_preservesNegligible hTarget

/-- The same generic theorem accepts a composed code transformation. -/
example (hTarget : SecureOnWithin bitGoal bitInterface.pptClass
    ((constantAnswerReduction.comp (Reduction.id bitGoal)).mapFamily bitFamily)) :
    SecureOnWithin bitGoal bitInterface.pptClass bitFamily := by
  let T := constantAnswerTransformation.comp
    (Reduction.MachineProgramTransformation.id bitInterface)
  exact (constantAnswerReduction.comp (Reduction.id bitGoal)).secureOnWithin_machinePPT
    bitInterface bitInterface bitFamily T
    (AdvantageBound.comp_preservesNegligible _ _
      AdvantageBound.id_preservesNegligible
      AdvantageBound.id_preservesNegligible) hTarget

/-- Polynomial multiplicative advantage loss remains a separate, compatible
condition on any reduction carrying the machine transformation witness. -/
example {R : Reduction bitGoal bitGoal} {p : Nat → Nat}
    (T : R.MachineProgramTransformation bitInterface bitInterface)
    (hp : PolynomiallyBounded p)
    (hLoss : R.loss = AdvantageBound.polynomialMultiplier p)
    (hTarget : SecureOnWithin bitGoal bitInterface.pptClass
      (R.mapFamily bitFamily)) :
    SecureOnWithin bitGoal bitInterface.pptClass bitFamily := by
  apply R.secureOnWithin_machinePPT bitInterface bitInterface bitFamily T
  · rw [hLoss]
    exact AdvantageBound.polynomialMultiplier_preservesNegligible hp
  · exact hTarget

end Machine.Examples
