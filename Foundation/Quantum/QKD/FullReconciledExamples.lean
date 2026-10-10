import Foundation.Quantum.QKD.FullReconciledRealSecrecy
import Foundation.Quantum.QKD.PairwiseReconciledRawExamples

/-! Concrete coherent four-signal attack: both the physical fixed-certificate
bound and the actual whole randomized experiment use the public-driven decoder.
The finite global error is not asserted to yield a useful key length. -/
namespace Foundation.Quantum.QKD.FullReconciledExamples
noncomputable section
open PairwisePhaseCoordinates PairwiseReconciledVerification PairwiseReconciledExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem physical_output : OperatorApprox
    (Subnormalized.joint (FullReconciledHash.fromDensity (tag := 1) (length := 1) (n := 4)
      (restoredRaw attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration)))
    (Subnormalized.joint (CommonKey.uniformize (FullReconciledHash.fromDensity (tag := 1) (length := 1) (n := 4)
      (restoredRaw attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration)))) (1/2) := by
  have h := full_physical_secrecy (tag := 1) (length := 1) (n := 4)
    attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration
  convert h using 1
  rw [privacyError, disclosure_coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

theorem actual_randomized_output : OperatorApprox
    (Subnormalized.joint (FullReconciledSecurity.realHash (tag := 1) (length := 1) attack 1 1 0))
    (Subnormalized.joint (CommonKey.uniformize
      (FullReconciledSecurity.realHash (tag := 1) (length := 1) attack 1 1 0)))
    (2 * PairwiseRandomizedSampling.error 4 1 0 + FullReconciledSecurity.globalPrivacyError 4 1 1 1 0 1 0) :=
  FullReconciledSecurity.real_verified_secrecy attack 1 0 1 0

end
end Foundation.Quantum.QKD.FullReconciledExamples
