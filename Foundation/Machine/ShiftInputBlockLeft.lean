import Foundation.Machine.TapeEquivalence
import Foundation.Machine.NativeSequence

namespace Machine.ShiftInputBlockLeft

/-- Physically shift a contiguous input block one cell to the left. Each bit
is read and written by native instructions. The vacated final cell is erased.
This joins a retained request and an arithmetic result across their separator. -/
def program : Program :=
  [.branch .input 11 1 6,
   .moveLeft .input, .write .input false, .moveRight .input, .moveRight .input, .jump 0,
   .moveLeft .input, .write .input true, .moveRight .input, .moveRight .input, .jump 0,
   .moveLeft .input, .erase .input, .halt]

private def start (before : List (Option Bool)) (previous : Option Bool)
    (bits : List Bool) (output : Tape) : Configuration :=
  {inputTape := {Tape.ofBits bits with left := previous::before}, outputTape := output}

private def finish (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  {pc := 13, inputTape := {left := bits.reverse.map some ++ before, right := [none]}, outputTape := output, halted := true}

private theorem bit_step (before : List (Option Bool)) (previous : Option Bool)
    (bit : Bool) (rest : List Bool) (output : Tape) :
    evalConfigWithin program (start before previous (bit::rest) output) 6 =
      PMF.pure (start (some bit::before) (some bit) rest output) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, start, Instruction.next,
      Configuration.advance, Configuration.tape, Configuration.updateTape, Tape.ofBits, Tape.moveLeft,
      Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem empty_step (before : List (Option Bool)) (previous : Option Bool) (output : Tape) :
    evalConfigWithin program (start before previous [] output) 4 =
      PMF.pure (finish before [] output) := by
  simp [evalConfigWithin, stepPMF, next, program, start, finish, Instruction.next,
    Configuration.advance, Configuration.tape, Configuration.updateTape, Tape.ofBits, Tape.moveLeft,
    Tape.write, PMF.pure_bind]

theorem eval (before : List (Option Bool)) (previous : Option Bool)
    (bits : List Bool) (output : Tape) :
    evalConfigWithin program (start before previous bits output) (6*bits.length+4) =
      PMF.pure (finish before bits output) := by
  induction bits generalizing before previous with
  | nil => simpa using empty_step before previous output
  | cons bit rest ih =>
    have time : 6*(bit::rest).length+4 = 6+(6*rest.length+4) := by simp; omega
    rw [time,
      evalConfigWithin_add, bit_step, PMF.pure_bind, ih]
    simp [finish, List.reverse_cons, List.map_append, List.append_assoc]

theorem runs (before : List (Option Bool)) (previous : Option Bool)
    (bits : List Bool) (output : Tape) :
    ∃ used, used ≤ 6*bits.length+4 ∧
      RunsFor program
        ({inputTape := {Tape.ofBits bits with left := previous::before}, outputTape := output} : Configuration)
        ({pc := 13, inputTape := {left := bits.reverse.map some ++ before, right := [none]}, outputTape := output, halted := true} : Configuration) used := by
  have member : finish before bits output ∈ (evalConfigWithin program (start before previous bits output) (6*bits.length+4)).support := by
    rw [eval]
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp member).toRunsFor_le

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

end Machine.ShiftInputBlockLeft
