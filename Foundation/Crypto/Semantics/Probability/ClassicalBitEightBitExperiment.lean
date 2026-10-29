import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSampler

/-! Exact joint key/ciphertext laws for executable table operations on eight bits.
The observation retains the secret key. Machine compilation remains separate. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal

def tableEncryptBit (v : OrderedGridVertex 32) (key : Fin 5) (message : Bool) : Bool :=
  if 0 ≤ tableCounts v key then message else !message

def tableEightBitResult (v : OrderedGridVertex 32) (message : Bool)
    (bits : Fin 8 → Bool) : Fin 5 × Bool :=
  let key := tableSampleEightBits v bits
  (key, tableEncryptBit v key message)

noncomputable def tableEightBitLaw (v : OrderedGridVertex 32) (message : Bool) :
    PMF (Fin 5 × Bool) :=
  (Foundation.Probability.uniform (Fin 8 → Bool)).map (tableEightBitResult v message)

theorem table_signed_nonneg_iff (v : OrderedGridVertex 32) (key : Fin 5) :
    0 ≤ (tableFiveCipher v).signed key ↔ 0 ≤ tableCounts v key := by
  change (0 : ℝ) ≤ (tableCounts v key : ℝ) / 256 ↔ (0 : ℤ) ≤ tableCounts v key
  rw [le_div_iff₀ (by norm_num)]
  simp

theorem tableEncryptBit_probability (v : OrderedGridVertex 32) (key : Fin 5)
    (message : Bool) :
    encryptionProbability (tableFiveCipher v).toCipher message key =
      if tableEncryptBit v key message then 0 else 1 := by
  by_cases h : 0 ≤ tableCounts v key <;> cases message <;>
    simp [encryptionProbability, PerfectCipher.toCipher, table_signed_nonneg_iff,
      tableEncryptBit, h]

theorem tableEncryptBit_correct (v : OrderedGridVertex 32) (key : Fin 5)
    (message : Bool) :
    tableEncryptBit v key (tableEncryptBit v key message) = message := by
  by_cases h : 0 ≤ tableCounts v key <;> cases message <;> simp [tableEncryptBit, h]

theorem tableEncryptBit_atom_factor (v : OrderedGridVertex 32) (key : Fin 5)
    (message ciphertext : Bool) :
    (if ciphertext then 1 - encryptionProbability (tableFiveCipher v).toCipher message key
      else encryptionProbability (tableFiveCipher v).toCipher message key) =
        if tableEncryptBit v key message = ciphertext then (1 : ℝ) else 0 := by
  rw [tableEncryptBit_probability]
  cases tableEncryptBit v key message <;> cases ciphertext <;> norm_num

theorem tableEightBitLaw_atom (v : OrderedGridVertex 32) (message : Bool)
    (key : Fin 5) (ciphertext : Bool) :
    (Foundation.Probability.eventProb (tableEightBitLaw v message)
      (fun result => result = (key, ciphertext))).toReal =
    (tableFiveCipher v).toCipher.weight key *
      (if ciphertext then 1 - encryptionProbability (tableFiveCipher v).toCipher message key
        else encryptionProbability (tableFiveCipher v).toCipher message key) := by
  classical
  rw [tableEncryptBit_atom_factor]
  unfold tableEightBitLaw
  rw [Foundation.Probability.eventProb_map]
  by_cases h : tableEncryptBit v key message = ciphertext
  · have he : (fun bits => tableEightBitResult v message bits = (key, ciphertext)) =
        (fun bits => tableSampleEightBits v bits = key) := by
      funext bits
      apply propext
      constructor
      · intro hh
        exact congrArg Prod.fst hh
      · intro hh
        simp [tableEightBitResult, hh, h]
    rw [he, tableSampleEightBits_cipher_weight]
    simp [h]
  · have he : (fun bits => tableEightBitResult v message bits = (key, ciphertext)) =
        (fun _ : Fin 8 → Bool => False) := by
      funext bits
      apply propext
      constructor
      · intro hh
        have hk : tableSampleEightBits v bits = key := congrArg Prod.fst hh
        have hc := congrArg Prod.snd hh
        exact h (by simpa [tableEightBitResult, hk] using hc)
      · exact False.elim
    rw [he]
    simp [Foundation.Probability.eventProb, h]

noncomputable def tableEightBitJointDistance (u v : OrderedGridVertex 32)
    (message : Bool) : ℝ :=
  (∑ key : Fin 5,
    (|(Foundation.Probability.eventProb (tableEightBitLaw u message)
        (fun result => result = (key, false))).toReal -
      (Foundation.Probability.eventProb (tableEightBitLaw v message)
        (fun result => result = (key, false))).toReal| +
     |(Foundation.Probability.eventProb (tableEightBitLaw u message)
        (fun result => result = (key, true))).toReal -
      (Foundation.Probability.eventProb (tableEightBitLaw v message)
        (fun result => result = (key, true))).toReal|)) / 2

theorem tableEightBitJointDistance_eq_jointTV (u v : OrderedGridVertex 32) (message : Bool) :
    tableEightBitJointDistance u v message =
      jointTV (tableFiveCipher u).toCipher (tableFiveCipher v).toCipher message := by
  simp only [tableEightBitJointDistance, tableEightBitLaw_atom, Bool.false_eq_true,
    ↓reduceIte, jointTV]

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
