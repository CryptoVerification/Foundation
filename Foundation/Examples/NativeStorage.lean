import Foundation.Crypto.Semantics.Machine.Storage
import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Machine.PreparedXor

/-! Reuse the same peak-storage theorem for key sampling and prepared XOR.
Widths are arbitrary and the programs are the existing finite native code. -/
namespace Foundation.Examples.NativeStorage
open Foundation.Probability

theorem keygen_peak (width elapsed : Nat) (hElapsed : elapsed ≤ 5 * width + 2)
    (state : Machine.Configuration)
    (h : state ∈ (TimedExecution.eval (Machine.stepPMF (Machine.PrivateBitGeneration.native width).code)
      elapsed ((Machine.PrivateBitGeneration.native width).execution.entry ())).support) :
    state.tapeCells ≤ 6 * width + 4 := by
  have hb := (Machine.PrivateBitGeneration.native width).tapeCells_prefix () elapsed hElapsed state h
  have hi := Machine.Tape.cells_ofBits_le (List.replicate width true)
  simp only [List.length_replicate] at hi
  change state.tapeCells ≤
    (Machine.Configuration.initial (List.replicate width true)).tapeCells + (5 * width + 2) at hb
  have hEntry : (Machine.Configuration.initial (List.replicate width true)).tapeCells ≤ width + 2 := by
    change (Machine.Tape.ofBits (List.replicate width true)).cells + 1 ≤ width + 2
    omega
  omega

theorem xor_peak (input : Machine.PairPreparation.Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ 8 * input.first.length + 2) (state : Machine.Configuration)
    (h : state ∈ (TimedExecution.eval
      (Machine.stepPMF Machine.OneTimePad.Prepared.listProcedure.code) elapsed
      (Machine.OneTimePad.Prepared.listProcedure.execution.entry input)).support) :
    state.tapeCells ≤ 10 * input.first.length + 4 := by
  have hb := Machine.OneTimePad.Prepared.listProcedure.tapeCells_prefix input elapsed hElapsed state h
  have hl := Machine.PairPreparation.interleave_length input.first input.second input.sameLength
  have hc : (Machine.PairPreparation.fromCells
      ((Machine.PairPreparation.interleave input.first input.second).map some ++ [none])).cells =
      2 * input.first.length + 1 := by
    cases he : Machine.PairPreparation.interleave input.first input.second with
    | nil => simp [he] at hl; simp [Machine.PairPreparation.fromCells, Machine.Tape.cells]; omega
    | cons bit rest =>
        simp [Machine.PairPreparation.fromCells, Machine.Tape.cells]
        simp [he] at hl
        omega
  change state.tapeCells ≤
    (Machine.PairPreparation.fromCells
      ((Machine.PairPreparation.interleave input.first input.second).map some ++ [none])).cells +
      1 + (8 * input.first.length + 2) at hb
  rw [hc] at hb
  omega

end Foundation.Examples.NativeStorage
