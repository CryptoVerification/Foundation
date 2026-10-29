import Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicSampler
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitBoundary

/-! The concrete table's exact key law from eight independent fair bits.
This does not yet compile the decoder to a bounded Foundation machine run. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal

def tableNaturalCounts (v : OrderedGridVertex 32) (k : Fin 5) : ℕ :=
  (tableCounts v k).natAbs

theorem tableNaturalCounts_sum (v : OrderedGridVertex 32) :
    ∑ k, tableNaturalCounts v k = 256 := by
  have hc : (∑ k, (tableNaturalCounts v k : ℤ)) = 256 := by
    simpa [tableNaturalCounts, tableCounts] using (table_vertex_checked v).2.1
  exact_mod_cast hc

def tableSampleEightBits (v : OrderedGridVertex 32) (bits : Fin 8 → Bool) : Fin 5 :=
  sampleCounts (tableNaturalCounts v) (by simpa using tableNaturalCounts_sum v)
    (bitIndexEquiv 8 bits)

theorem tableSampleEightBits_probability (v : OrderedGridVertex 32) (k : Fin 5) :
    Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin 8 → Bool))
      (fun bits => tableSampleEightBits v bits = k) =
        (tableNaturalCounts v k : ℝ≥0∞) / 256 := by
  simpa [tableSampleEightBits] using sampleCounts_bits_event_probability 8
    (tableNaturalCounts v) (by simpa using tableNaturalCounts_sum v) k

theorem tableSampleEightBits_cipher_weight (v : OrderedGridVertex 32) (k : Fin 5) :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (Fin 8 → Bool))
      (fun bits => tableSampleEightBits v bits = k)).toReal =
        (tableFiveCipher v).toCipher.weight k := by
  rw [tableSampleEightBits_probability]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  change (tableNaturalCounts v k : ℝ) / 256 = |(tableCounts v k : ℝ) / 256|
  simp [tableNaturalCounts, abs_div]

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
