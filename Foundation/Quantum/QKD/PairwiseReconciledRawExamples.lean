import Foundation.Quantum.QKD.PairwiseReconciledRestoration
import Foundation.Quantum.QKD.PairwiseReconciledExamples
import Foundation.Quantum.QKD.ArbitraryReconciliationExamples

/-! Nonzero suffix survives the fixed public-record representation, and
the coherent attacked physical raw density runs the same actual decoder,
check and two independently seeded hashes with the proved privacy bound. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledRawExamples
noncomputable section
open PairwisePhaseCoordinates PairwiseReconciledVerification PairwiseReconciledExamples
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

/-- Five public bits in a nine-position record; the transmitted suffix is 1. -/
theorem public_record : ArbitraryReconciliation.messageRecord
    (show ArbitraryReconciliation.publicBits 7 ≤ 9 by decide)
    (ArbitraryReconciliation.message (ArbitraryReconciliationExamples.alice 1)) =
      ![0,0,0,0,1,0,0,0,0] := by decide

/-- Bob's seven bits have three errors. The specified public record alone
supplies the message used by his actual decoder. -/
theorem bob_from_public : ArbitraryReconciliation.decode (ArbitraryReconciliationExamples.bob 1)
    (ArbitraryReconciliation.messageFromRecord (show ArbitraryReconciliation.publicBits 7 ≤ 9 by decide)
      ![0,0,0,0,1,0,0,0,0]) = ArbitraryReconciliationExamples.alice 1 := by
  rw [← public_record, ArbitraryReconciliation.message_roundtrip]
  exact ArbitraryReconciliationExamples.decoded 1

theorem recovered_physical : OperatorApprox
    (Subnormalized.joint (ReconciledHash.fromDensity (tag := 1) (length := 1) (n := 4)
      Finset.univ configuration.2 (recoveredRaw attack Finset.univ 1 0 1 0 configuration)))
    (Subnormalized.joint (CommonKey.uniformize (ReconciledHash.fromDensity (tag := 1) (length := 1) (n := 4)
      Finset.univ configuration.2 (recoveredRaw attack Finset.univ 1 0 1 0 configuration)))) (1/2) := by
  have h := recovered_physical_secrecy (tag := 1) (length := 1) (n := 4)
    attack Finset.univ 1 0 1 0 configuration
  convert h using 1
  rw [privacyError, disclosure_coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

theorem restored_public_output : OperatorApprox
    (Subnormalized.joint (finishedHash (tag := 1) (length := 1) (n := 4)
      attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration))
    (Subnormalized.joint (CommonKey.uniformize (finishedHash (tag := 1) (length := 1) (n := 4)
      attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration))) (1/2) := by
  have h := finished_secrecy (tag := 1) (length := 1) (n := 4)
    attack Finset.univ (fun _ => .Z) 1 0 1 0 configuration
  convert h using 1
  rw [privacyError, disclosure_coefficient]
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseReconciledRawExamples
