import Foundation.Crypto.Semantics.Machine.GuardedTape
import Foundation.Examples.GuardedCompiler

namespace Machine.Examples

open GuardedCompiler

def guardedLogicalTape : Tape :=
  { left := [some false, none], current := some true, right := [none, some false] }

example : (encodeTape [some true, none, some false] guardedLogicalTape).cells = 15 :=
  encodeTape_cells _ _

example : (encodeTape [some true, none, some false] guardedLogicalTape).left.drop 6 =
    [some true, none, some false] := rfl

example : (encodeTape [] guardedLogicalTape).current = some true ∧
    (encodeTape [] guardedLogicalTape).right.head? = some (some true) :=
  encodeTape_pair _ _

example (before : List (Option Bool)) (logical : Tape) (cell : Option Bool) :
    VirtualCell.replacePair (encodeTape before logical) (VirtualCell.code cell) =
      encodeTape before (logical.write cell) := encodeTape_write before logical cell

example (before : List (Option Bool)) (logical : Tape) :
    VirtualCell.moveRightTape (encodeTape before logical) =
      encodeTape before logical.moveRight := encodeTape_moveRight before logical

example (source : Program) (c d : Configuration) (step : Step source c d)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ 17 * (c.inputTape.cells + c.outputTape.cells) + 23 ∧
      RunsFor (compile source) (encodeConfiguration source.length beforeInput beforeOutput c)
        (encodeConfiguration source.length beforeInput beforeOutput d) used :=
  compile_step_runs source c d step beforeInput beforeOutput

/-- Three consecutive compiled blocks execute on the same represented
tapes. The second block chooses the true random branch, and the third
returns to the source's instruction 1. The saved prefixes are arbitrary.
The initial representation is a precondition, not a free input-preparation
operation; this example does not assert that the looping program is PPT. -/
example (beforeInput beforeOutput : List (Option Bool)) :
    RunsFor (compile guardedSource)
      (encodeConfiguration guardedSource.length beforeInput beforeOutput
        (Configuration.initial [true, false]))
      (encodeConfiguration guardedSource.length beforeInput beforeOutput
        ({ pc := 1
           inputTape := Tape.ofBits [true, false]
           outputTape := { current := some true } } : Configuration)) 15 := by
  let source0 := Configuration.initial [true, false]
  let source1 := (source0.updateTape .output (fun t => t.write (some false))).advance
  let source2 := (source1.updateTape .output (fun t => t.write (some true))).advance
  have first := compile_write_encoded_runs guardedSource 0 .output (some false)
    (by decide) rfl source0 rfl rfl beforeInput beforeOutput
  have second := compile_randomBit_encoded_runs guardedSource 1 .output
    (by decide) rfl source1 rfl rfl beforeInput beforeOutput true
  have third := compile_branch_encoded_runs guardedSource 2 .output 9 0 1
    (by decide) rfl source2 rfl rfl beforeInput beforeOutput
  exact (first.trans second).trans third

example (beforeInput beforeOutput : List (Option Bool)) (logical : Configuration)
    (hPc : logical.pc = 3) (hActive : logical.halted = false) :
    ∃ used, used ≤ 17 * logical.outputTape.cells + 23 ∧
      RunsFor (compile guardedSource)
        (encodeConfiguration guardedSource.length beforeInput beforeOutput logical)
        (encodeConfiguration guardedSource.length beforeInput beforeOutput
          (logical.updateTape .output Tape.moveLeft).advance) used :=
  compile_moveLeft_encoded_runs guardedSource 3 .output (by decide) rfl
    logical hPc hActive beforeInput beforeOutput

end Machine.Examples
