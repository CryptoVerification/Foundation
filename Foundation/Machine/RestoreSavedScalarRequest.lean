import Foundation.Machine.SavedFramedScalarSampler
import Foundation.Machine.ConsumedInputErasure

namespace Machine.RestoreSavedScalarRequest

/-- Erase only the saved width counter, then rewind the still-present
public request. The sampled scalar on the other tape is untouched. -/
def program : Program := ConsumedInputErasure.program.followedBy rewindBitstring

theorem runs (width : Nat) (request : List Bool) (output : Tape) :
    ∃ target used, used ≤ 4*width + 2*request.length + 8 ∧
      RunsFor program
        ({inputTape := {left := List.replicate width (some true) ++ none::request.reverse.map some},
          outputTape := output} : Configuration) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits request) ∧
      target.outputTape.Equivalent output := by
  let counter := List.replicate width true
  have eraseRun := (eraseOutputBlock_runs output (request.reverse.map some) counter []).swapTapes
  let erased := (eraseOutputBlockFinish output (request.reverse.map some) counter []).swapTapes
  have rewindRun := rewindBitstring_runs_from request none (List.replicate (width+1) none) output
  have layout :
      ({inputTape := {left := request.reverse.map some, right := List.replicate (width+1) none},
        outputTape := output} : Configuration).Equivalent (erased.resumeAt 0) := by
    have same : erased.inputTape =
        {left := request.reverse.map some, right := List.replicate (width+1) none} := by
      change ({left := request.reverse.map some, right := List.replicate (counter.reverse.length+1) none ++ []} : Tape) = _
      simp [counter]
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    change ({left := request.reverse.map some, right := List.replicate (width+1) none} : Tape).Equivalent erased.inputTape
    rw [same]
    exact Tape.Equivalent.refl _

  obtain ⟨target, used, bound, run, halted, input, saved⟩ :=
    eraseRun.followedBy_equivalent rewindRun layout (Nat.zero_le _) rfl rfl rfl
  have restored :
      (({right := request.map some ++ none::List.replicate (width+1) none} : Tape).moveRight).Equivalent
        (Tape.ofBits request) := by
    have h := rewindBitstring_saved_input_equivalent request [] (width+1)
    refine h.trans ⟨rfl, ?_, fun _ => rfl⟩
    intro i
    cases request <;> cases i <;> rfl
  refine ⟨target, used, ?_, ?_, halted, input.symm.trans restored, saved.symm⟩
  · simp only [counter, List.length_replicate] at bound
    omega
  · change RunsFor (ConsumedInputErasure.program.followedBy rewindBitstring)
      ({inputTape := {left := counter.reverse.map some ++ none::request.reverse.map some},
        outputTape := output} : Configuration) target used at run
    simpa [program, counter] using run

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _
    (Program.swapTapes_no_randomBit _ eraseOutputBlock_no_randomBit) rewindBitstring_no_randomBit tape


end Machine.RestoreSavedScalarRequest
