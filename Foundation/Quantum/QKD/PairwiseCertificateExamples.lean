import Foundation.Quantum.QKD.PairwiseFinalCertificate

/-! Full randomized, finalized two-signal attacked experiment. This validates
the restored certificate and sampling-error transport; it is not a claim that
this small instance generates a secure final key. -/
namespace Foundation.Quantum.QKD.PairwiseCertificateExamples
noncomputable section
open PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

theorem attacked_final :
    StateApprox (Hashing.linearState (length := 1) PairwiseAttackExamples.attack 1 1 0)
      (finalCertificate PairwiseAttackExamples.attack 1 1 1 0
        (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) Hashing.rawHash)
      ((1/4:ℝ)*Real.sqrt (1/2)) := by
  have h := final_certificate_approximation PairwiseAttackExamples.attack 1 1 1 0
    (Foundation.Probability.uniform (Hashing.RawSeed 2 1)) Hashing.rawHash
  rw [PairwiseRandomizedSampling.two_signal_total_error] at h
  exact h

end
end Foundation.Quantum.QKD.PairwiseCertificateExamples
