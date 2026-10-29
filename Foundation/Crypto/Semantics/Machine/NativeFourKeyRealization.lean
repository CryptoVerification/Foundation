import Foundation.Crypto.Semantics.Machine.NativeFourKeyDecryption
import Foundation.Crypto.Semantics.Machine.NativeFiveKeyRealization

/-! A concrete nonempty class of native four-key candidates for the prescribed
boundary comparison. Internal key/ciphertext observations are explicit.
This is not a key-hidden security or general reduction-impossibility theorem. -/
namespace Machine.NativeFourKeyRealization
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

noncomputable def encryption : NativeCipherRealization.Encryption (Fin 4) where
  bounded := NativeControlledFourKeyCipher.bounded
  request := NativeControlledFourKeyCipher.rawInput
  observe := NativeFourKeySampler.observe
  observe_equivalent := NativeFourKeySampler.observe_equivalent
  profile := fun v => (FourKeyWitness.cipher v).toCipher
  realizes := by
    intro v message key ciphertext
    change (eventProb ((evalConfigWithin NativeControlledFourKeyCipher.code
      (Configuration.initial (NativeControlledFourKeyCipher.rawInput v message)) 148).map
      NativeFourKeySampler.observe) (· = some (key, ciphertext))).toReal = _
    rw [NativeControlledFourKeyCipher.atom_probability, fourEightBitLaw_atom]
    rfl

noncomputable def decryption : NativeCipherRealization.Decryption encryption.profile where
  bounded := NativeFourKeyDecryption.bounded
  request := NativeFourKeyDecryption.rawInput
  observe := NativeKeyPairDecisionExecution.readDecision
  observe_equivalent := NativeKeyPairDecisionExecution.readDecision_equivalent
  realizes := NativeFourKeyDecryption.atom_probability

noncomputable def family : NativeCipherRealization.Family (Fin 4) where
  encryption := encryption
  decryption := decryption

theorem encryption_budget (n : ℕ) : family.encryption.bounded.budget n = 148 := rfl

theorem decryption_budget (n : ℕ) : family.decryption.bounded.budget n = 69 := rfl

theorem boundary (v : NativeCipherRealization.Vertex)
    (h : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    (FourKeyWitness.cipher v).signed = tableFourVector v := FourKeyWitness.boundary v h

theorem candidate_exists :
    ∃ F : NativeCipherRealization.Family (Fin 4),
      (∀ v, F.encryption.profile v = (FourKeyWitness.cipher v).toCipher) ∧
      (∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
        (FourKeyWitness.cipher v).signed = tableFourVector v) :=
  ⟨family, fun _ => rfl, boundary⟩

theorem edge_lower :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      ∀ message, 2 / 3 ≤ family.encryption.distance u v message :=
  NativeCipherRealization.perfect_four_key_lower family FourKeyWitness.cipher (fun _ => rfl) boundary

theorem five_key_gap :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      NativeFiveKeyRealization.family.encryption.distance u v message + 145 / 384 ≤
        family.encryption.distance u v message := by
  obtain ⟨u, v, edge, gap⟩ := NativeCipherRealization.perfect_four_key_gap
    family FourKeyWitness.cipher (fun _ => rfl) boundary
  exact ⟨u, v, edge, fun message => by rw [NativeFiveKeyRealization.distance_eq]; exact gap message⟩

end Machine.NativeFourKeyRealization
