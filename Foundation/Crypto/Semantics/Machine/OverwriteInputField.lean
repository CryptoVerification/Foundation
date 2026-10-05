import Foundation.Crypto.Semantics.Machine.TapeEquivalence

namespace Machine.OverwriteInputField

/-- Copy the output bit block into an input field one cell at a time. The
source block is retained, and input cells after the equal-width field are
untouched. This lets sampled scalar bits become an arithmetic operand. -/
def program : Program :=
  [.branch .output 8 1 3, .write .input false, .jump 5,
   .write .input true, .jump 5, .moveRight .input,
   .moveRight .output, .jump 0, .halt]

def start (beforeInput beforeOutput : List (Option Bool))
    (old following bits : List Bool) : Configuration :=
  {inputTape := {Tape.ofBits (old++following) with left := beforeInput},
   outputTape := {Tape.ofBits bits with left := beforeOutput}}

def finish (beforeInput beforeOutput : List (Option Bool))
    (following bits : List Bool) : Configuration :=
  {pc := 8, halted := true,
   inputTape := {Tape.ofBits following with left := bits.reverse.map some ++ beforeInput},
   outputTape := {left := bits.reverse.map some ++ beforeOutput}}

theorem runs (beforeInput beforeOutput : List (Option Bool))
    (old following bits : List Bool) (hLength : old.length = bits.length) :
    RunsFor program (start beforeInput beforeOutput old following bits)
      (finish beforeInput beforeOutput following bits) (6*bits.length+2) := by
  induction bits generalizing old beforeInput beforeOutput with
  | nil =>
    have empty : old = [] := List.length_eq_zero_iff.mp (by simpa using hLength)
    subst old
    let first := start beforeInput beforeOutput [] following []
    have select : Step program first {first with pc := 8} := by
      simp [Step, successors, next, program, first, start, Tape.ofBits,
        Instruction.next, Configuration.tape]
    have halt : Step program {first with pc := 8} (finish beforeInput beforeOutput following []) := by
      simp [Step, successors, next, program, first, start, finish, Tape.ofBits, Instruction.next]
    exact ((RunsFor.zero _).succ select).succ halt
  | cons bit rest ih =>
    cases old with
    | nil => simp at hLength
    | cons previous remaining =>
      have lengths : remaining.length = rest.length := by simpa using hLength
      let first := start beforeInput beforeOutput (previous::remaining) following (bit::rest)
      let selected := {first with pc := if bit then 3 else 1}
      let written := {first with pc := if bit then 4 else 2, inputTape := first.inputTape.write (some bit)}
      let joined := {written with pc := 5}
      let inputMoved := {joined with pc := 6, inputTape := joined.inputTape.moveRight}
      let outputMoved := {inputMoved with pc := 7, outputTape := inputMoved.outputTape.moveRight}
      have one : Step program first selected := by
        cases bit <;> simp [Step, successors, next, program, first, selected,
          start, Tape.ofBits, Instruction.next, Configuration.tape]
      have two : Step program selected written := by
        cases bit <;> simp [Step, successors, next, program, selected, written,
          Instruction.next, Configuration.updateTape, Configuration.advance, first, start]
      have three : Step program written joined := by
        cases bit <;> simp [Step, successors, next, program, written, joined, first, start, Instruction.next]
      have four : Step program joined inputMoved := by
        cases bit <;> simp [Step, successors, next, program, joined, inputMoved,
          written, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
      have five : Step program inputMoved outputMoved := by
        cases bit <;> simp [Step, successors, next, program, inputMoved, outputMoved,
          joined, written, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
      have six : Step program outputMoved
          (start (some bit::beforeInput) (some bit::beforeOutput) remaining following rest) := by
        cases rest <;> cases remaining <;> cases following <;> cases bit <;>
          simp [Step, successors, next, program, outputMoved, inputMoved, joined, written,
            first, start, Tape.ofBits, Tape.moveRight, Tape.write, Instruction.next]
      have prefixRun := ((((((RunsFor.zero _).succ one).succ two).succ three).succ four).succ five).succ six
      have finalEq : finish (some bit::beforeInput) (some bit::beforeOutput) following rest =
          finish beforeInput beforeOutput following (bit::rest) := by
        simp [finish, List.reverse_cons, List.map_append, List.append_assoc]
      have whole := prefixRun.trans (ih _ _ _ lengths)
      rw [finalEq] at whole
      convert whole using 1 <;> simp only [first, List.length_cons] <;> omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by simp [program]

end Machine.OverwriteInputField
