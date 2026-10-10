import Foundation.Quantum.QKD.FullReconciledSecurity
import Foundation.Quantum.QKD.FullReconciledExamples

/-! Full normalized randomized BB84 with a coherent four-signal attack.
These examples use the actual decoder and both real final keys, including
all abort branches. The finite error expression is not a useful-key claim. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurityExamples
noncomputable section
open Subnormalized PairwiseReconciledExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Includes the original abort and verifier-failure branches at their weights. -/
theorem normalized :
    (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0).matrix.trace = 1 :=
  (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0).normalized

/-- Actual mismatch event of the full physical output, including abort. -/
theorem mismatch_probability :
    (recordEvent (qubits 4) (fun r =>
      let o : IdealKey.Output (FullReconciledHash.Public 4 1 1) 1 := (Fintype.equivFin _).symm r
      o.aliceKey ≠ o.bobKey)).probability
      (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0) ≤ 1/2 := by
  have h := FullReconciledHash.full_correctness (tag := 1) (length := 1)
    (readDensity (Randomized.keyState attack 1 1 0)) (mass_ofCQ _)
  simpa [FullReconciledSecurity.realState, IdealKey.Key, Fintype.card_fun, Fintype.card_fin] using h

/-- Idealization preserves the public packet and aborts and replaces only
accepted private keys by an equal independent uniform pair. -/
theorem secure :
    IdealKey.Secure (FullReconciledSecurity.realState (tag := 1) (length := 1) attack 1 1 0)
      (1/2 + (2 * PairwiseRandomizedSampling.error 4 1 0 +
        FullReconciledSecurity.globalPrivacyError 4 1 1 1 0 1 0)) := by
  have h := FullReconciledSecurity.real_verified_secure (tag := 1) (length := 1) attack 1 0 1 0
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.FullReconciledSecurityExamples
