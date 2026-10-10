import Foundation.Quantum.QKD.PairwiseConditionalHashProcess
import Foundation.Quantum.QKD.PairwiseFinishedExamples

/-! Secrecy of the accepted hash obtained directly from the same existing
conditional raw certificate for a nontrivial coherent block attack. -/
namespace Foundation.Quantum.QKD.PairwiseConditionalProcessExamples
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

theorem attacked_conditional :
    OperatorApprox
      (Subnormalized.joint (AcceptedHash.fromDensity
        (conditionalCertificate PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2))
          (fun _ => .Z) 1 0 1 0)
        (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) Hashing.rawHash))
      (Subnormalized.joint (CommonKey.uniformize (AcceptedHash.fromDensity
        (conditionalCertificate PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2))
          (fun _ => .Z) 1 0 1 0)
        (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) Hashing.rawHash)))
      (conditionalPrivacyError (length := 1) (Finset.univ : Finset (Fin 2)) 1 0 1 0 (by decide)) :=
  conditional_certificate_secrecy _ _ _ _ _ _ _ (by decide)

end
end Foundation.Quantum.QKD.PairwiseConditionalProcessExamples
