import Foundation.Machine.SavedBitstringRewind
import Foundation.Machine.NativeSequence

namespace Machine.RewindReturnedRequest

private def leftOnce : Program := [.moveLeft .input, .halt]

/-- Walk back across the returned arithmetic result and the separator,
then across the retained request. Both blocks stay in their actual cells. -/
def program : Program := (rewindBitstring.followedBy leftOnce).followedBy rewindBitstring

theorem runs (request result : List Bool) (tail : List (Option Bool)) (output : Tape)
    (hResult : result ≠ []) :
    ∃ target used, used ≤ 2*result.length+2*request.length+12 ∧
      RunsFor program
        ({inputTape := {left := result.reverse.map some ++ none::request.reverse.map some, right := tail},
          outputTape := output} : Configuration) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        ({({right := request.map some ++ none::result.map some ++ none::tail} : Tape).moveRight with left := [none]} : Tape) ∧
      target.outputTape.Equivalent output := by
  have resultRewind := rewindBitstring_runs_saved result (request.reverse.map some) none tail output
  cases result with
  | nil => exact False.elim (hResult rfl)
  | cons bit bits =>
    let positioned : Configuration := {pc := 1, halted := true, inputTape := {left := request.reverse.map some, right := (bit::bits).map some ++ none::tail}, outputTape := output}
    have leftRun : RunsFor leftOnce
        ({inputTape := {left := none::request.reverse.map some, current := some bit, right := bits.map some ++ none::tail}, outputTape := output} : Configuration)
        positioned 2 := by
      let entry : Configuration := {inputTape := {left := none::request.reverse.map some, current := some bit, right := bits.map some ++ none::tail}, outputTape := output}
      let moved : Configuration := {pc := 1, inputTape := entry.inputTape.moveLeft, outputTape := output}
      have one : Step leftOnce entry moved := by simp [Step, successors, next, leftOnce, entry, moved, Instruction.next, Configuration.updateTape, Configuration.advance]
      have two : Step leftOnce moved positioned := by simp [Step, successors, next, leftOnce, positioned, moved, entry, Tape.moveLeft, Instruction.next]
      exact ((RunsFor.zero _).succ one).succ two
    obtain ⟨middle, a, ha, first, halted, input, out⟩ := resultRewind.followedBy_equivalent leftRun
      (Configuration.Equivalent.refl _) (Nat.zero_le _) rfl rfl rfl
    have requestRewind := rewindBitstring_runs_from request none ((bit::bits).map some ++ none::tail) output
    have layout : ({inputTape := {left := request.reverse.map some, right := (bit::bits).map some ++ none::tail}, outputTape := output} : Configuration).Equivalent (middle.resumeAt 0) :=
      ⟨rfl, rfl, input, out⟩
    obtain ⟨target, used, bound, run, halt, ti, tout⟩ := first.followedBy_equivalent requestRewind layout
      (Nat.zero_le _) rfl halted rfl
    refine ⟨target, used, by omega, run, halt, ?_, tout.symm⟩
    cases request <;> simpa [Tape.moveRight] using ti.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · exact rewindBitstring_no_randomBit
    · intro tape; simp [leftOnce]
  · exact rewindBitstring_no_randomBit

end Machine.RewindReturnedRequest
