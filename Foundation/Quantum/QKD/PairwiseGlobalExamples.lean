import Foundation.Quantum.QKD.PairwiseGlobalSecrecy
import Foundation.Quantum.QKD.PairwiseConditionalProcessExamples

/-! The same nontrivial coherent attack, now with every selected set and
unmatched basis averaged. The finite error formula includes zero accepted
contribution from insufficient-test abort branches. -/
namespace Foundation.Quantum.QKD.PairwiseGlobalExamples
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

theorem attacked_global :
    OperatorApprox
      (Subnormalized.joint (globalAcceptedHash (length := 1) PairwiseAttackExamples.attack 1 0 1 0))
      (Subnormalized.joint (CommonKey.uniformize
        (globalAcceptedHash (length := 1) PairwiseAttackExamples.attack 1 0 1 0)))
      (privacyError 2 1 1 0 1 0) :=
  global_accepted_secrecy _ _ _ _ _

theorem insufficient_empty_selected :
    AcceptedHash.fromDensity
      (conditionalCertificate PairwiseAttackExamples.attack (∅ : Finset (Fin 2)) (fun _ => .Z) 1 0 1 0)
      (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) Hashing.rawHash = Subnormalized.zero :=
  conditional_insufficient_zero _ _ _ _ _ _ _ (by decide) _ _

end
end Foundation.Quantum.QKD.PairwiseGlobalExamples
