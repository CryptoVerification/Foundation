import Foundation.Crypto.Semantics.Machine.NativeFiveKeyDecryption

/-! A concrete cipher-family contract with native encryption and decryption.
The encryption observation includes private key labels; it is an internal
semantic view, not a public-output adversary. The separate time bounds do not
assign a free runtime to a caller preparing or composing the requests. -/
namespace Machine.NativeFiveKeyRealization
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

noncomputable def encryption : NativeCipherRealization.Encryption (Fin 5) where
  bounded := NativePreparedKeyDecision.bounded
  request := NativePreparedKeyDecision.rawInput
  observe := NativePreparedInternalResult.observe
  observe_equivalent := NativePreparedInternalResult.observe_equivalent
  profile := fun v => (tableFiveCipher v).toCipher
  realizes := by
    intro v message key ciphertext
    change (eventProb ((evalConfigWithin NativePreparedKeyDecision.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map
      NativePreparedInternalResult.observe) (· = some (key, ciphertext))).toReal = _
    rw [NativePreparedInternalResult.atom_probability, tableEightBitLaw_atom]
    rfl

noncomputable def decryption : NativeCipherRealization.Decryption encryption.profile where
  bounded := NativeFiveKeyDecryption.bounded
  request := NativeFiveKeyDecryption.rawInput
  observe := NativeKeyPairDecisionExecution.readDecision
  observe_equivalent := NativeKeyPairDecisionExecution.readDecision_equivalent
  realizes := NativeFiveKeyDecryption.atom_probability

noncomputable def family : NativeCipherRealization.Family (Fin 5) where
  encryption := encryption
  decryption := decryption

theorem encryption_budget (n : ℕ) : family.encryption.bounded.budget n = 930 := rfl

theorem decryption_budget (n : ℕ) : family.decryption.bounded.budget n = 69 := rfl

theorem profile (v : NativeCipherRealization.Vertex) :
    family.encryption.profile v = (tableFiveCipher v).toCipher := rfl

theorem distance_eq (u v : NativeCipherRealization.Vertex) (message : Bool) :
    family.encryption.distance u v message = NativePreparedInternalResult.jointDistance u v message := by
  rw [NativeCipherRealization.Encryption.distance_eq,
    NativePreparedInternalResult.jointDistance_eq, tableEightBitJointDistance_eq_jointTV]
  rfl

theorem edge_bound (u v : NativeCipherRealization.Vertex)
    (edge : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    family.encryption.distance u v message ≤ 37 / 128 := by
  rw [distance_eq]
  exact NativePreparedInternalResult.edge_bound u v edge message

end Machine.NativeFiveKeyRealization
