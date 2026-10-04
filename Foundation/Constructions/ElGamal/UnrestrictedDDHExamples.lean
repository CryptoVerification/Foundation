import Foundation.Constructions.ElGamal.UnrestrictedDDH
import Foundation.Constructions.ElGamal.ConcreteReductionExamples

namespace ElGamal.UnrestrictedDDHExamples

open Foundation.Probability
open ElGamal.ConcreteExamples ElGamal.ConcreteReductionExamples
open scoped ENNReal

/-- A concrete check of the probability-gap convention: for two scalars,
the unrestricted distinguisher has advantage `1 - 1/2 = 1/2`. -/
example : ddhAdvantage bitParams bitSampling
    (unrestrictedDDHAdversary bitParams bitAlgebra) = 1 / 2 := by
  change ddhAdvantage bitParams bitAlgebra.sampling _ = _
  rw [unrestrictedDDH_advantage]
  change 1 - (Fintype.card Bool : ℝ≥0∞)⁻¹ = 1 / 2
  norm_num

/-- The unrestricted premise in the old two-element transport example is
actually false. This supplies an explicit adversary, not a hardness claim. -/
theorem bitFamily_not_secureDDH_all :
    ¬ SecureOnWithin (DDH ProbComp (concreteDDHSemantics bitSamplingFamily))
      (AdversaryClass.all _) (fun _ => bitParams) := by
  apply not_secureDDH_all bitSamplingFamily (fun _ => bitParams) (fun _ => bitAlgebra)
  · intro n
    simp [bitSamplingFamily, bitAlgebra]
  · intro n
    change 2 ≤ Fintype.card Bool
    norm_num

end ElGamal.UnrestrictedDDHExamples
