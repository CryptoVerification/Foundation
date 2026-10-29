import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitObserverBound
import Foundation.Crypto.Semantics.Probability.FiniteVariationWitness

/-! Replace the semantic real-mass likelihood test by exact integer counts.
This supplies a computable finite predicate, without a native runtime claim. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Foundation.Probability
open scoped ENNReal

def tableAtomCount (v : OrderedGridVertex 32) (message : Bool) (result : Fin 5 × Bool) : ℕ :=
  if tableEncryptBit v result.1 message = result.2 then tableNaturalCounts v result.1 else 0

theorem table_atom_real_count (v : OrderedGridVertex 32) (message : Bool) (result : Fin 5 × Bool) :
    (tableEightBitLaw v message result).toReal = (tableAtomCount v message result : ℝ) / 256 := by
  have hw : (tableFiveCipher v).toCipher.weight result.1 = (tableNaturalCounts v result.1 : ℝ) / 256 := by
    rw [← tableSampleEightBits_cipher_weight v result.1, tableSampleEightBits_probability]
    simp [ENNReal.toReal_div]
  rw [tableEightBitLaw_mass, tableEightBitLaw_atom, tableEncryptBit_atom_factor, hw]
  by_cases h : tableEncryptBit v result.1 message = result.2 <;> simp [tableAtomCount, h]

def tableCountTest (u v : OrderedGridVertex 32) (message : Bool) (result : Fin 5 × Bool) : Bool :=
  decide (tableAtomCount v message result ≤ tableAtomCount u message result)

theorem positiveTest_eq_countTest (u v : OrderedGridVertex 32) (message : Bool) :
    positiveTest (tableEightBitLaw u message) (tableEightBitLaw v message) =
      tableCountTest u v message := by
  funext result
  unfold positiveTest tableCountTest
  congr 1
  apply propext
  rw [table_atom_real_count, table_atom_real_count,
    div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 256)]
  exact_mod_cast (Iff.rfl : tableAtomCount v message result ≤ tableAtomCount u message result ↔
    tableAtomCount v message result ≤ tableAtomCount u message result)

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
