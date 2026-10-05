import Foundation.Crypto.Semantics.Machine.TapeEquivalence

namespace Machine.MoveInputLeftByOutput

/-- A physical bit-block counter moves the input head left once per bit.
The input cells and counter bits are preserved. No numerical offset is a
machine instruction. -/
def program : Program :=
  [.branch .output 4 1 1, .moveLeft .input, .moveRight .output, .jump 0, .halt]

def start (input : Tape) (before : List (Option Bool)) (counter : List Bool) : Configuration :=
  {inputTape := input, outputTape := {Tape.ofBits counter with left := before}}

def finish (input : Tape) (before : List (Option Bool)) (counter : List Bool) : Configuration :=
  {pc := 4, halted := true, inputTape := (Tape.moveLeft^[counter.length]) input,
    outputTape := {left := counter.reverse.map some ++ before}}

theorem runs (input : Tape) (before : List (Option Bool)) (counter : List Bool) :
    RunsFor program (start input before counter) (finish input before counter) (4*counter.length+2) := by
  induction counter generalizing input before with
  | nil =>
    let first := start input before []
    have one : Step program first {first with pc := 4} := by
      simp [Step, successors, next, program, first, start, Tape.ofBits, Instruction.next, Configuration.tape]
    have two : Step program {first with pc := 4} (finish input before []) := by
      simp [Step, successors, next, program, first, start, finish, Tape.ofBits, Instruction.next]
    exact ((RunsFor.zero _).succ one).succ two
  | cons bit rest ih =>
    let first := start input before (bit::rest)
    let selected := {first with pc := 1}
    let moved := {first with pc := 2, inputTape := input.moveLeft}
    let outputMoved := {moved with pc := 3, outputTape := moved.outputTape.moveRight}
    have one : Step program first selected := by
      cases bit <;> simp [Step, successors, next, program, first, selected, start, Tape.ofBits, Instruction.next, Configuration.tape]
    have two : Step program selected moved := by
      simp [Step, successors, next, program, selected, moved, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
    have three : Step program moved outputMoved := by
      simp [Step, successors, next, program, moved, outputMoved, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
    have four : Step program outputMoved (start input.moveLeft (some bit::before) rest) := by
      cases rest <;> simp [Step, successors, next, program, outputMoved, moved, first,
        start, Tape.ofBits, Tape.moveRight, Instruction.next]
    have prefixRun := ((((RunsFor.zero _).succ one).succ two).succ three).succ four
    have same : finish input.moveLeft (some bit::before) rest = finish input before (bit::rest) := by
      simp [finish, Function.iterate_succ_apply, List.reverse_cons, List.map_append, List.append_assoc]
    have result := prefixRun.trans (ih input.moveLeft (some bit::before))
    rw [same] at result
    convert result using 1 <;> simp only [List.length_cons] <;> omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by simp [program]

end Machine.MoveInputLeftByOutput
