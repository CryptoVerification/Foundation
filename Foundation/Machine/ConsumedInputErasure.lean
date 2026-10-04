import Foundation.Machine.BitstringErasure
import Foundation.Machine.TapeSwap
import Foundation.Machine.TapeEquivalence

namespace Machine.ConsumedInputErasure

/-- The existing five-instruction block eraser with tapes exchanged. It
erases the consumed request on the input tape while preserving the output
columns that will become the arithmetic input. -/
def program : Program := eraseOutputBlock.swapTapes

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> rfl
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ] using ih i

theorem outer_blank (bits : List Bool) :
    ({ left := bits.reverse.map some } : Tape).Equivalent
      { left := bits.reverse.map some ++ [none] } := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  exact (getD_append_blank (bits.reverse.map some) i).symm

theorem runs (bits : List Bool) (savedOutput : Tape) :
    let start : Configuration :=
      { inputTape := { left := bits.reverse.map some ++ [none] },
        outputTape := savedOutput }
    ∃ target used,
      used ≤ 4 * bits.length + 3 ∧
      RunsFor program start target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent ({} : Tape) ∧
      target.outputTape = savedOutput := by
  dsimp only
  let sourceStart := eraseOutputBlockStart savedOutput [] bits []
  let sourceFinish := eraseOutputBlockFinish savedOutput [] bits []
  let target := sourceFinish.swapTapes
  refine ⟨target, 4 * bits.length + 3, le_refl _, ?_, rfl, ?_, rfl⟩
  · have hRun := (eraseOutputBlock_runs savedOutput [] bits []).swapTapes
    let explicitStart : Configuration :=
      { inputTape := { left := bits.reverse.map some ++ [none] },
        outputTape := savedOutput }
    change RunsFor program explicitStart target (4 * bits.length + 3) at hRun
    simpa [explicitStart] using hRun
  · change ({ left := [], right := List.replicate (bits.reverse.length + 1) none ++ [] } : Tape).Equivalent
      ({} : Tape)
    simpa using (Tape.blank_padding_equivalent [] (bits.length + 1))

/-- Erasing the already-consumed input region also terminates on arbitrary
physical tapes, including malformed frames and internal blanks. -/
theorem runs_any (input output : Tape) :
    ∃ target used,
      used ≤ 4 * input.left.length + 3 ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        target used ∧
      target.halted = true ∧ target.outputTape = output := by
  obtain ⟨target, used, hUsed, run, hHalt, hPreserved, _⟩ :=
    eraseOutputBlock_terminates_from_anyTape output input
  refine ⟨target.swapTapes, used, hUsed, ?_, ?_, ?_⟩
  · simpa [program, Configuration.swapTapes] using run.swapTapes
  · simpa [Configuration.swapTapes] using hHalt
  · simpa [Configuration.swapTapes] using hPreserved

end Machine.ConsumedInputErasure
