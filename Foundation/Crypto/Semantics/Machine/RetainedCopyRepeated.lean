import Foundation.Crypto.Semantics.Machine.RetainedCopy

/-! Exact physical reuse of the retained-copy program. The blank cells left
by a preceding call remain represented throughout the next call. -/
namespace Machine.RetainedCopy
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def copyingRetained (before remaining : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { inputTape := { restored (remaining.map some ++ [none]) with
      left := before.reverse.map some ++ [none] },
    outputTape := { left := outputBefore } }

def rewindingRetained (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 8, inputTape := ⟨left.map some ++ [none], current, right⟩, outputTape := output }

theorem copy_retained_cell (bit : Bool) (before remaining : List Bool)
    (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copyingRetained before (bit :: remaining) outputBefore) 6 =
      PMF.pure (copyingRetained (before ++ [bit]) remaining (some bit :: outputBefore)) := by
  cases bit <;> cases remaining <;>
    simp [evalConfigWithin, stepPMF, next, code, copyingRetained, restored,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.reverse_append]

theorem copy_retained_loop (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copyingRetained before remaining outputBefore) (6 * remaining.length + 1) =
      PMF.pure (rewindingRetained (before ++ remaining).reverse none []
        { left := remaining.reverse.map some ++ outputBefore }) := by
  induction remaining generalizing before outputBefore with
  | nil => simp [evalConfigWithin, stepPMF, next, code, copyingRetained,
      rewindingRetained, restored, Instruction.next, Configuration.tape]
  | cons bit remaining ih =>
      rw [show 6 * (bit :: remaining).length + 1 = 6 + (6 * remaining.length + 1) by simp; omega,
        evalConfigWithin_add, copy_retained_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_retained_cell (bit : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewindingRetained (bit :: left) current right output) 2 =
      PMF.pure (rewindingRetained left (some bit) (current :: right) output) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, code, rewindingRetained, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft]

theorem rewind_retained_loop (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewindingRetained left current right output) (2 * left.length + 4) =
      PMF.pure ({ pc := 11, inputTape := restored (left.reverse.map some ++ current :: right), outputTape := output, halted := true } : Configuration) := by
  induction left generalizing current right with
  | nil => simp [evalConfigWithin, stepPMF, next, code, rewindingRetained, restored,
      Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, Tape.moveRight]
  | cons bit left ih =>
      rw [show 2 * (bit :: left).length + 4 = 2 + (2 * left.length + 4) by simp; omega,
        evalConfigWithin_add, rewind_retained_cell, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- A subsequent invocation has precisely the same physical exit as the
first invocation, without replacing the input tape by an equivalent tape. -/
theorem run_retained (key : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code
      { inputTape := restored (key.map some ++ [none]), outputTape := { left := outputBefore } }
      (8 * key.length + 5) = PMF.pure (finish key outputBefore) := by
  change evalConfigWithin code (copyingRetained [] key outputBefore) _ = _
  rw [show 8 * key.length + 5 = (6 * key.length + 1) + (2 * key.reverse.length + 4) by simp; omega,
    evalConfigWithin_add, copy_retained_loop, PMF.pure_bind]
  simpa [finish] using rewind_retained_loop key.reverse none []
    ({ left := key.reverse.map some ++ outputBefore } : Tape)

end Machine.RetainedCopy
