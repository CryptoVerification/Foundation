import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitExperiment

/-! An executable four-key witness with the prescribed boundary. Integer
counts select a key using eight fair bits; signed counts choose a reversible
one-bit pad. These are semantic laws, before native compilation. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal

namespace FourKeyWitness

def onBoundary (v : OrderedGridVertex 32) : Prop :=
  EightBitTable.boundary (v.val 0).val (v.val 1).val (v.val 2).val

instance (v : OrderedGridVertex 32) : Decidable (onBoundary v) := by
  unfold onBoundary EightBitTable.boundary
  infer_instance

def counts (v : OrderedGridVertex 32) (k : Fin 4) : ℤ :=
  if onBoundary v then tableFourCounts v k
  else if k.val = 0 then 128 else if k.val = 1 then -128 else 0

theorem counts_valid (v : OrderedGridVertex 32) :
    (∑ k, counts v k) = 0 ∧ (∑ k, |counts v k|) = 256 := by
  by_cases h : onBoundary v
  · simpa only [counts, if_pos h] using
      table_boundary_counts_valid v ((table_boundary_iff v).mpr h)
  · simp only [counts, if_neg h]
    decide +kernel

noncomputable def cipher (v : OrderedGridVertex 32) : PerfectCipher (Fin 4) :=
  dyadicPerfectCipher 256 (by omega) (counts v) (counts_valid v).1 (counts_valid v).2

theorem boundary (v : OrderedGridVertex 32)
    (h : ∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) :
    (cipher v).signed = tableFourVector v := by
  have hb : onBoundary v := (table_boundary_iff v).mp h
  funext k
  change (counts v k : ℝ) / 256 = (tableFourCounts v k : ℝ) / 256
  rw [counts, if_pos hb]

end FourKeyWitness

def fourNaturalCounts (v : OrderedGridVertex 32) (k : Fin 4) : ℕ :=
  (FourKeyWitness.counts v k).natAbs

theorem fourNaturalCounts_sum (v : OrderedGridVertex 32) :
    ∑ k, fourNaturalCounts v k = 256 := by
  have hc : (∑ k, (fourNaturalCounts v k : ℤ)) = 256 := by
    simpa [fourNaturalCounts, FourKeyWitness.counts] using (FourKeyWitness.counts_valid v).2
  exact_mod_cast hc

def fourSampleEightBits (v : OrderedGridVertex 32) (bits : Fin 8 → Bool) : Fin 4 :=
  sampleCounts (fourNaturalCounts v) (by simpa using fourNaturalCounts_sum v)
    (bitIndexEquiv 8 bits)

theorem fourSampleEightBits_probability (v : OrderedGridVertex 32) (k : Fin 4) :
    Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin 8 → Bool))
      (fun bits => fourSampleEightBits v bits = k) =
        (fourNaturalCounts v k : ℝ≥0∞) / 256 := by
  simpa [fourSampleEightBits] using sampleCounts_bits_event_probability 8
    (fourNaturalCounts v) (by simpa using fourNaturalCounts_sum v) k

theorem fourSampleEightBits_cipher_weight (v : OrderedGridVertex 32) (k : Fin 4) :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin 8 → Bool))
      (fun bits => fourSampleEightBits v bits = k)).toReal =
        (FourKeyWitness.cipher v).toCipher.weight k := by
  rw [fourSampleEightBits_probability]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  change (fourNaturalCounts v k : ℝ) / 256 = |(FourKeyWitness.counts v k : ℝ) / 256|
  simp [fourNaturalCounts, abs_div]

def fourEncryptBit (v : OrderedGridVertex 32) (key : Fin 4) (message : Bool) : Bool :=
  if 0 ≤ FourKeyWitness.counts v key then message else !message

def fourEightBitResult (v : OrderedGridVertex 32) (message : Bool)
    (bits : Fin 8 → Bool) : Fin 4 × Bool :=
  let key := fourSampleEightBits v bits
  (key, fourEncryptBit v key message)

noncomputable def fourEightBitLaw (v : OrderedGridVertex 32) (message : Bool) :
    PMF (Fin 4 × Bool) :=
  (Foundation.Probability.uniform (Fin 8 → Bool)).map (fourEightBitResult v message)

theorem four_signed_nonneg_iff (v : OrderedGridVertex 32) (key : Fin 4) :
    0 ≤ (FourKeyWitness.cipher v).signed key ↔ 0 ≤ FourKeyWitness.counts v key := by
  change (0 : ℝ) ≤ (FourKeyWitness.counts v key : ℝ) / 256 ↔ (0 : ℤ) ≤ FourKeyWitness.counts v key
  rw [le_div_iff₀ (by norm_num)]
  simp

theorem fourEncryptBit_probability (v : OrderedGridVertex 32) (key : Fin 4)
    (message : Bool) :
    encryptionProbability (FourKeyWitness.cipher v).toCipher message key =
      if fourEncryptBit v key message then 0 else 1 := by
  by_cases h : 0 ≤ FourKeyWitness.counts v key <;> cases message <;>
    simp [encryptionProbability, PerfectCipher.toCipher, four_signed_nonneg_iff,
      fourEncryptBit, h]

theorem fourEncryptBit_correct (v : OrderedGridVertex 32) (key : Fin 4)
    (message : Bool) :
    fourEncryptBit v key (fourEncryptBit v key message) = message := by
  by_cases h : 0 ≤ FourKeyWitness.counts v key <;> cases message <;> simp [fourEncryptBit, h]

theorem fourEncryptBit_atom_factor (v : OrderedGridVertex 32) (key : Fin 4)
    (message ciphertext : Bool) :
    (if ciphertext then 1 - encryptionProbability (FourKeyWitness.cipher v).toCipher message key
      else encryptionProbability (FourKeyWitness.cipher v).toCipher message key) =
        if fourEncryptBit v key message = ciphertext then (1 : ℝ) else 0 := by
  rw [fourEncryptBit_probability]
  cases fourEncryptBit v key message <;> cases ciphertext <;> norm_num

theorem fourEightBitLaw_atom (v : OrderedGridVertex 32) (message : Bool)
    (key : Fin 4) (ciphertext : Bool) :
    (Foundation.Probability.eventProb (fourEightBitLaw v message)
      (fun result => result = (key, ciphertext))).toReal =
    (FourKeyWitness.cipher v).toCipher.weight key *
      (if ciphertext then 1 - encryptionProbability (FourKeyWitness.cipher v).toCipher message key
        else encryptionProbability (FourKeyWitness.cipher v).toCipher message key) := by
  classical
  rw [fourEncryptBit_atom_factor]
  unfold fourEightBitLaw
  rw [Foundation.Probability.eventProb_map]
  by_cases h : fourEncryptBit v key message = ciphertext
  · have he : (fun bits => fourEightBitResult v message bits = (key, ciphertext)) =
        (fun bits => fourSampleEightBits v bits = key) := by
      funext bits
      apply propext
      constructor
      · intro hh
        exact congrArg Prod.fst hh
      · intro hh
        simp [fourEightBitResult, hh, h]
    rw [he, fourSampleEightBits_cipher_weight]
    simp [h]
  · have he : (fun bits => fourEightBitResult v message bits = (key, ciphertext)) =
        (fun _ : Fin 8 → Bool => False) := by
      funext bits
      apply propext
      constructor
      · intro hh
        have hk : fourSampleEightBits v bits = key := congrArg Prod.fst hh
        have hc := congrArg Prod.snd hh
        exact h (by simpa [fourEightBitResult, hk] using hc)
      · exact False.elim
    rw [he]
    simp [Foundation.Probability.eventProb, h]


end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
