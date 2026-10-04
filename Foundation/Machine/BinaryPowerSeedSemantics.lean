import Foundation.Machine.BinaryPowerSeed
import Foundation.Machine.BinaryProductSemantics

namespace Machine.BinaryPowerSeedSemantics

open BinaryProductSelection BinaryProductSemantics

private theorem zeros_value {α : Type} (items : List α) :
    Binary.value (items.map fun _ => false) = 0 := by
  induction items with
  | nil => rfl
  | cons _ rest ih => simp only [List.map_cons, Binary.value, Bool.toNat_false, ih, Nat.mul_zero, Nat.add_zero]

/-- The charged seed write turns an initially zero accumulator into one.
The mathematical projection here does not replace that machine write. -/
theorem seeded_initial_accumulator (raw : List BinaryModularAddition.Column)
    (hNonempty : raw ≠ []) :
    Binary.value ((BinaryPowerSeed.seeded (initialColumns raw)).map Column.accumulator) = 1 := by
  cases raw with
  | nil => exact (hNonempty rfl).elim
  | cons column rest =>
      simp only [initialColumns, List.map_cons, BinaryPowerSeed.seeded, Column.accumulator,
        Binary.value, Bool.toNat_true]
      have hZero : Binary.value ((rest.map fun column : BinaryModularAddition.Column =>
          { accumulator := false, operand := column.1.1, modulus := column.2,
            multiplier := column.1.2, pending := true : Column }).map Column.accumulator) = 0 := by
        simpa only [List.map_map, Function.comp_def] using zeros_value rest
      rw [hZero]

theorem seeded_initial_operand (raw : List BinaryModularAddition.Column) :
    (BinaryPowerSeed.seeded (initialColumns raw)).map Column.operand =
      raw.map fun column => column.1.1 := by
  cases raw <;> simp [BinaryPowerSeed.seeded, initialColumns, List.map_map, Function.comp_def]

theorem seeded_initial_modulus (raw : List BinaryModularAddition.Column) :
    (BinaryPowerSeed.seeded (initialColumns raw)).map Column.modulus = raw.map Prod.snd := by
  cases raw <;> simp [BinaryPowerSeed.seeded, initialColumns, List.map_map, Function.comp_def]

theorem seeded_initial_remaining (raw : List BinaryModularAddition.Column) :
    remainingBits (BinaryPowerSeed.seeded (initialColumns raw)) = raw.map fun column => column.1.2 := by
  cases raw <;> simp [remainingBits, BinaryPowerSeed.seeded, initialColumns,
    List.filterMap_map, Function.comp_def]

end Machine.BinaryPowerSeedSemantics
