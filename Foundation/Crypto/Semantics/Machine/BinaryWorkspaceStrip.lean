import Foundation.Crypto.Semantics.Machine.BinaryWorkspacePreparation

namespace Machine.BinaryWorkspaceStrip

/-- Remove one high workspace bit from a result whose output head is just
past the fixed-width result. A caller must prove this head-position contract;
reading the mathematical result list alone is insufficient. -/
def program : Program :=
  [.moveLeft .output, .erase .output, .halt]

def start (input : Tape) (bits : List Bool) : Configuration :=
  { inputTape := input,
    outputTape := { left := (bits ++ [false]).reverse.map some } }

def finish (input : Tape) (bits : List Bool) : Configuration :=
  { pc := 2, inputTape := input,
    outputTape := ((start input bits).outputTape.moveLeft).write none,
    halted := true }

/-- The high bit is erased by one head move and one cell operation. -/
theorem runs (input : Tape) (bits : List Bool) :
    RunsFor program (start input bits) (finish input bits) 3 := by
  let moved : Configuration :=
    { pc := 1, inputTape := input,
      outputTape := (start input bits).outputTape.moveLeft }
  let erased : Configuration :=
    { moved with pc := 2, outputTape := moved.outputTape.write none }
  have hMove : Step program (start input bits) moved := by
    simp [Step, successors, next, program, moved, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hErase : Step program moved erased := by
    simp [Step, successors, next, program, moved, erased, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hHalt : Step program erased (finish input bits) := by
    simp [Step, successors, next, program, moved, erased, finish, start,
      Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hMove) hErase) hHalt

/-- The same three instructions halt from any two tapes. The result is
specified as the actual left move and erase, without assuming an output
layout on malformed input. -/
theorem runs_any (input output : Tape) :
    RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 2, inputTape := input,
         outputTape := output.moveLeft.write none,
         halted := true } : Configuration) 3 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let moved : Configuration :=
    { pc := 1, inputTape := input, outputTape := output.moveLeft }
  let erased : Configuration :=
    { pc := 2, inputTape := input, outputTape := output.moveLeft.write none }
  have hMove : Step program start moved := by
    simp [Step, successors, next, program, start, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hErase : Step program moved erased := by
    simp [Step, successors, next, program, moved, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hHalt : Step program erased
      ({ erased with halted := true } : Configuration) := by
    simp [Step, successors, next, program, erased, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hMove) hErase) hHalt

private theorem getD_append_none (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- The spare outer blank and represented right blanks after product
finalization do not change the cells seen by the strip program. -/
theorem padded_output_equivalent (bits : List Bool) (blanks : Nat) :
    ({ left := (bits ++ [false]).reverse.map some ++ [none],
       right := List.replicate blanks none } : Tape).Equivalent
      { left := (bits ++ [false]).reverse.map some } := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    exact getD_append_none _ i
  · exact (Tape.blank_padding_equivalent _ blanks).2.2

@[simp] theorem finish_outputBits (input : Tape) (bits : List Bool) :
    (finish input bits).outputBits = bits := by
  simp [Configuration.outputBits, finish, start, Tape.bits, Tape.moveLeft, Tape.write,
    List.reverse_append, List.filterMap_append]

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp [program]

end Machine.BinaryWorkspaceStrip
