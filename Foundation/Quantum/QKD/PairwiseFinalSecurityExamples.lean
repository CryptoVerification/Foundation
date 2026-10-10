import Foundation.Quantum.QKD.PairwiseFinalSecurity
import Foundation.Quantum.QKD.PairwiseRealExamples

/-! Full existing finalization and ideal resource for the coherent attack.
The explicit actual mismatch cost is retained; this is not a claim that error
correction, authentication, or useful finite-key parameters are established. -/
namespace Foundation.Quantum.QKD.PairwiseFinalSecurityExamples
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

theorem attacked_full_output :
    IdealKey.Secure (Hashing.linearState (length := 1) PairwiseAttackExamples.attack 1 1 0)
      (finalCorrectnessCost (length := 1) PairwiseAttackExamples.attack 1 1 0 +
        (2*PairwiseRandomizedSampling.error 2 1 1 + privacyError 2 1 1 1 1 0)) :=
  final_security_with_actual_cost _ _ _ _ _

end
end Foundation.Quantum.QKD.PairwiseFinalSecurityExamples
