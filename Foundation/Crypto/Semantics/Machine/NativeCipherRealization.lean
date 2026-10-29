import Foundation.Crypto.Semantics.Machine.NativePreparedInternalResult

/-! Explicit finite-code contracts for labelled cipher families. Encryption
and decryption each have a bounded native program, specified raw requests,
cell-invariant result views, and atom-by-atom realization of one shared cipher
profile. Views are semantic observations; request preparation by a further
caller still requires its own native execution contract. -/
namespace Machine.NativeCipherRealization
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators

abbrev Vertex := OrderedGridVertex 32

noncomputable def encryptionAtom {Key : Type} [Fintype Key] (c : Cipher Key)
    (message ciphertext : Bool) (key : Key) : ℝ :=
  c.weight key * (if ciphertext then 1 - encryptionProbability c message key else encryptionProbability c message key)

noncomputable def decryptionAtom {Key : Type} [Fintype Key] (c : Cipher Key)
    (key : Key) (ciphertext message : Bool) : ℝ :=
  let zeroProbability := if ciphertext then c.dec1 key else c.dec0 key
  if message then 1 - zeroProbability else zeroProbability

structure Encryption (Key : Type) [Fintype Key] where
  bounded : CryptoLogic.BoundedProgram
  request : Vertex → Bool → List Bool
  observe : Configuration → Option (Key × Bool)
  observe_equivalent : ∀ c d, c.Equivalent d → observe c = observe d
  profile : Vertex → Cipher Key
  realizes : ∀ v message key ciphertext,
    (eventProb ((evalConfigWithin bounded.program (Configuration.initial (request v message))
      (bounded.budget (request v message).length)).map observe) (· = some (key, ciphertext))).toReal =
      encryptionAtom (profile v) message ciphertext key

structure Decryption {Key : Type} [Fintype Key] (profile : Vertex → Cipher Key) where
  bounded : CryptoLogic.BoundedProgram
  request : Vertex → Key → Bool → List Bool
  observe : Configuration → Option Bool
  observe_equivalent : ∀ c d, c.Equivalent d → observe c = observe d
  realizes : ∀ v key ciphertext message,
    (eventProb ((evalConfigWithin bounded.program (Configuration.initial (request v key ciphertext))
      (bounded.budget (request v key ciphertext).length)).map observe) (· = some message)).toReal =
      decryptionAtom (profile v) key ciphertext message

structure Family (Key : Type) [Fintype Key] where
  encryption : Encryption Key
  decryption : Decryption encryption.profile

namespace Encryption
variable {Key : Type} [Fintype Key] (E : Encryption Key)

noncomputable def law (v : Vertex) (message : Bool) : PMF (Option (Key × Bool)) :=
  (evalConfigWithin E.bounded.program (Configuration.initial (E.request v message))
    (E.bounded.budget (E.request v message).length)).map E.observe

theorem executes (v : Vertex) (message : Bool) :
    HaltsWithin E.bounded.program (E.request v message) (E.bounded.budget (E.request v message).length) :=
  E.bounded.halts _

theorem polynomial_time : PolynomialTime E.bounded.program := E.bounded.polynomialTime

theorem atom_probability (v : Vertex) (message : Bool) (key : Key) (ciphertext : Bool) :
    (eventProb (E.law v message) (· = some (key, ciphertext))).toReal =
      encryptionAtom (E.profile v) message ciphertext key := E.realizes v message key ciphertext

noncomputable def distance (u v : Vertex) (message : Bool) : ℝ :=
  (∑ key,
    (|(eventProb (E.law u message) (· = some (key, false))).toReal -
      (eventProb (E.law v message) (· = some (key, false))).toReal| +
     |(eventProb (E.law u message) (· = some (key, true))).toReal -
      (eventProb (E.law v message) (· = some (key, true))).toReal|)) / 2

theorem distance_eq (u v : Vertex) (message : Bool) :
    E.distance u v message = jointTV (E.profile u) (E.profile v) message := by
  unfold distance jointTV
  simp only [atom_probability, encryptionAtom, Bool.false_eq_true, if_false, if_true]

noncomputable def comparisonDistance (u v : Vertex) : ℝ := max (E.distance u v false) (E.distance u v true)

theorem comparisonDistance_eq (u v : Vertex) :
    E.comparisonDistance u v = implementationDistance (E.profile u) (E.profile v) := by
  unfold comparisonDistance implementationDistance
  rw [distance_eq, distance_eq]

end Encryption

namespace Decryption
variable {Key : Type} [Fintype Key] {profile : Vertex → Cipher Key} (D : Decryption profile)

theorem executes (v : Vertex) (key : Key) (ciphertext : Bool) :
    HaltsWithin D.bounded.program (D.request v key ciphertext)
      (D.bounded.budget (D.request v key ciphertext).length) := D.bounded.halts _

theorem polynomial_time : PolynomialTime D.bounded.program := D.bounded.polynomialTime

end Decryption

theorem perfect_four_key_lower (F : Family (Fin 4)) (perfect : Vertex → PerfectCipher (Fin 4))
    (profile : ∀ v, F.encryption.profile v = (perfect v).toCipher)
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (perfect v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message, 2 / 3 ≤ F.encryption.distance u v message := by
  obtain ⟨u, v, edge, lower⟩ := table_four_key_obstruction perfect boundary
  exact ⟨u, v, edge, fun message => by rw [Encryption.distance_eq, profile u, profile v]; exact lower message⟩

theorem perfect_four_key_gap (F : Family (Fin 4)) (perfect : Vertex → PerfectCipher (Fin 4))
    (profile : ∀ v, F.encryption.profile v = (perfect v).toCipher)
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (perfect v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      NativePreparedInternalResult.jointDistance u v message + 145 / 384 ≤ F.encryption.distance u v message := by
  obtain ⟨u, v, edge, gap⟩ := NativePreparedInternalResult.perfect_four_key_gap perfect boundary
  exact ⟨u, v, edge, fun message => by rw [Encryption.distance_eq, profile u, profile v]; exact gap message⟩

theorem perfect_four_key_not_cap (F : Family (Fin 4)) (perfect : Vertex → PerfectCipher (Fin 4))
    (profile : ∀ v, F.encryption.profile v = (perfect v).toCipher)
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (perfect v).signed = tableFourVector v)
    (cap : ℝ) (strict : cap < 2 / 3) :
    ¬ (∀ u v, faceEdge (orderedGridComplex 32) u v → ∀ message, F.encryption.distance u v message ≤ cap) := by
  intro all
  obtain ⟨u, v, edge, lower⟩ := perfect_four_key_lower F perfect profile boundary
  have lo := lower false
  have hi := all u v edge false
  linarith

theorem approximate_four_key_gap (F : Family (Fin 4)) (ε δ : Vertex → ℝ)
    (h0 : ∀ v, ∑ k, (F.encryption.profile v).weight k * error0 (F.encryption.profile v) k ≤ δ v)
    (h1 : ∀ v, ∑ k, (F.encryption.profile v).weight k * error1 (F.encryption.profile v) k ≤ δ v)
    (hp : ∀ v, |bias (signedContrast (F.encryption.profile v))| ≤ ε v)
    (hm : ∀ v, ε v + 2 * δ v ≤ 1 / 8)
    (boundary : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      repair (signedContrast (F.encryption.profile v)) = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      NativePreparedInternalResult.comparisonDistance u v + 1 / 384 ≤ F.encryption.comparisonDistance u v := by
  obtain ⟨u, v, edge, gap⟩ := NativePreparedInternalResult.approximate_four_key_gap F.encryption.profile ε δ h0 h1 hp hm boundary
  exact ⟨u, v, edge, by rw [Encryption.comparisonDistance_eq]; exact gap⟩

end Machine.NativeCipherRealization
