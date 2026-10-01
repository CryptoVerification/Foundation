import Foundation.Machine.GuardedSimulation
import Foundation.Examples.VirtualCell

namespace Machine.Examples

open GuardedCompiler Foundation.Probability

/-- A finite source fixture contains randomness, a backward branch, an
out-of-range branch, both movement directions, erasure, and explicit halt.
The examples below certify individual compiled blocks on caller tapes.
They do not assert that this looping source terminates on every input. -/
def guardedSource : Program :=
  [.write .output false, .randomBit .output, .branch .output 9 0 1,
   .moveLeft .output, .moveRight .input, .erase .output, .jump 100, .halt]

example : (compile guardedSource).length = 545 := by
  rw [compile_length]
  rfl

example : compile [] = [.halt] := rfl

example (source : Program) : compileCode (Program.encode source) =
    some (Program.encode (compile source)) := compileCode_encode source

/-- The source's backward edge to zero remains an absolute edge to zero.
It is not accidentally rebased as an internal subroutine address. -/
example : (compile guardedSource)[144]? = some (.jump 0) := by decide
example : (compile guardedSource)[148]? = some (.jump 68) := by decide

/-- The invalid source address 9 selects the real terminal halt at 544. -/
example : (compile guardedSource)[140]? = some (.jump 544) := by decide
example : (compile guardedSource)[544]? = some .halt :=
  compile_getElem?_terminal guardedSource

/-- The boundary probe calls the real growth subroutine at offset 17 of
the fourth block. Its first branch has actual rebased local targets. -/
example : (compile guardedSource)[218]? = some (.jump 221) := by decide
example : (compile guardedSource)[221]? =
    some (.branch .output 225 222 222) := by decide

example (cell : Option Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor (compile guardedSource)
      ((VirtualCell.pairStart .output (VirtualCell.code cell) before after other).rebasePc 136)
      ({ VirtualCell.pairStart .output (VirtualCell.code cell) before after other with
        pc := match cell with | none => 544 | some false => 0 | some true => 68 } :
          Configuration) 5 := by
  have run := compile_branch_runs guardedSource 2 .output 9 0 1 (by decide) rfl
    cell before after other
  cases cell with
  | none => exact run
  | some bit => cases bit <;> exact run

example (input output : Tape) :
    evalConfigWithin (compile guardedSource)
      ((VirtualCell.start input output).rebasePc 68) 5 =
      sampleBit.map (fun bit =>
        (VirtualCell.finish .output (some bit) input output).resumeAt 136) :=
  compile_randomBit_eval guardedSource 1 .output (by decide) rfl input output

example (bit : Bool) :
    RunsFor (compile guardedSource)
      ((VirtualCell.start savedCallerTape virtualCellInput).rebasePc 68)
      ((VirtualCell.finish .output (some bit) savedCallerTape virtualCellInput).resumeAt 136)
      5 := compile_randomBit_runs guardedSource 1 .output (by decide) rfl
    bit savedCallerTape virtualCellInput

/-- The compiled instruction contains one native random-bit transition;
the resulting data bit is exactly fair after restoring the head. -/
example (input output : Tape) :
    eventProb (evalConfigWithin (compile guardedSource)
      ((VirtualCell.start input output).rebasePc 68) 5)
      (fun c => c.outputTape.right.head? = some (some true)) = 1 / 2 := by
  have hEval : evalConfigWithin (compile guardedSource)
      ((VirtualCell.start input output).rebasePc 68) 5 =
      sampleBit.map (fun bit =>
        (VirtualCell.finish .output (some bit) input output).resumeAt 136) :=
    compile_randomBit_eval guardedSource 1 .output (by decide) rfl input output
  rw [hEval]
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  have hpre :
      ((fun bit => (VirtualCell.finish .output (some bit) input output).resumeAt 136) ⁻¹'
        {c : Configuration | c.outputTape.right.head? = some (some true)}) = {true} := by
    ext bit
    cases bit <;> simp [VirtualCell.finish, VirtualCell.start, VirtualCell.replacePair,
      VirtualCell.code, Configuration.updateTape, Configuration.resumeAt]
  rw [hpre]
  simp [sampleBit, uniform]

example : RunsFor (compile guardedSource)
    ((VirtualCell.start savedCallerTape virtualCellInput).rebasePc 0)
    ((VirtualCell.finish .output (some false) savedCallerTape virtualCellInput).resumeAt 68)
    5 := compile_write_runs guardedSource 0 .output (some false) (by decide) rfl
  savedCallerTape virtualCellInput

example : RunsFor (compile guardedSource)
    ((VirtualCell.start savedCallerTape virtualCellInput).rebasePc 340)
    ((VirtualCell.finish .output none savedCallerTape virtualCellInput).resumeAt 408)
    5 := compile_write_runs guardedSource 5 .output none (by decide) rfl
  savedCallerTape virtualCellInput

/-- Existing cells need four transitions. At the blank right frontier,
eight transitions create the new `00` pair using actual machine writes. -/
example : RunsFor (compile guardedSource)
    ((VirtualCell.start virtualCellInput savedCallerTape).rebasePc 272)
    ((VirtualCell.moveRightFinish .input virtualCellInput savedCallerTape).resumeAt 340)
    4 := compile_moveRight_runs guardedSource 4 .input (by decide) rfl
  virtualCellInput savedCallerTape

example : RunsFor (compile guardedSource)
    ((VirtualCell.start virtualCellFrontier savedCallerTape).rebasePc 272)
    ((VirtualCell.moveRightFinish .input virtualCellFrontier savedCallerTape).resumeAt 340)
    8 := compile_moveRight_runs guardedSource 4 .input (by decide) rfl
  virtualCellFrontier savedCallerTape

example (current previous : Option Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor (compile guardedSource)
      ((VirtualCell.leftStart .output (VirtualCell.code current) (VirtualCell.code previous)
        before after other).rebasePc 204)
      ({ VirtualCell.pairStart .output (VirtualCell.code previous) before
        (some (VirtualCell.code current).1 :: some (VirtualCell.code current).2 :: after)
        other with pc := 272 } : Configuration) 7 := by
  have run := compile_moveLeft_probe_runs guardedSource 3 .output (by decide) rfl
    (VirtualCell.code current) (VirtualCell.code previous) before after other
  simpa [VirtualCell.leftFinish, VirtualCell.moveLeftSteps,
    VirtualCell.code_ne_boundary previous, guardedSource, blockSize, address] using run

/-- The same guarded caller region is passed through the boundary probe
and the embedded growth code. Saved caller data is not replaced between
these two operational traces. -/
example (before : List (Option Bool)) (current : Option Bool)
    (rest : List (Option Bool)) (other : Tape) :
    ∃ used, used ≤ 17 * (current :: rest).length + 23 ∧
      RunsFor (compile guardedSource)
        ((VirtualCell.growLeftStart .output before (current :: rest) other).rebasePc 204)
        ((VirtualCell.growLeftFinish .output before (current :: rest) other).resumeAt 272)
        used := compile_moveLeft_boundary_runs guardedSource 3 .output (by decide) rfl
  before current rest other

example : ∃ used, used ≤ 74 ∧ RunsFor (compile guardedSource)
    ((VirtualCell.growLeftStart .output [some true, none]
      [some true, none, some false] savedCallerTape).rebasePc 204)
    ((VirtualCell.growLeftFinish .output [some true, none]
      [some true, none, some false] savedCallerTape).resumeAt 272) used :=
  compile_moveLeft_boundary_runs guardedSource 3 .output (by decide) rfl
    [some true, none] (some true) [none, some false] savedCallerTape

/-- This source also contains a random instruction. The boundary insertion
still returns in exactly 74 transitions with one full configuration as its
distribution, preserving the saved caller data and other tape. -/
example : RunsFor (compile guardedSource)
    ((VirtualCell.growLeftStart .output [some true, none]
      [some true, none, some false] savedCallerTape).rebasePc 204)
    ((VirtualCell.growLeftFinish .output [some true, none]
      [some true, none, some false] savedCallerTape).resumeAt 272) 74 :=
  compile_moveLeft_boundary_runs_exact guardedSource 3 .output (by decide) rfl
    [some true, none] (some true) [none, some false] savedCallerTape

example : evalConfigWithin (compile guardedSource)
    ((VirtualCell.growLeftStart .output [some true, none]
      [some true, none, some false] savedCallerTape).rebasePc 204) 74 =
    PMF.pure ((VirtualCell.growLeftFinish .output [some true, none]
      [some true, none, some false] savedCallerTape).resumeAt 272) :=
  compile_moveLeft_boundary_eval guardedSource 3 .output (by decide) rfl
    [some true, none] (some true) [none, some false] savedCallerTape

example (before : List (Option Bool)) (cell : Option Bool)
    (rest : List (Option Bool)) (other : Tape) (final : Configuration)
    (run : PaddedRunsFor (compile guardedSource)
      ((VirtualCell.growLeftStart .output before (cell :: rest) other).rebasePc 204)
      final (17 * (cell :: rest).length + 23)) :
    final = (VirtualCell.growLeftFinish .output before (cell :: rest) other).resumeAt 272 := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  have hEval : evalConfigWithin (compile guardedSource)
      ((VirtualCell.growLeftStart .output before (cell :: rest) other).rebasePc 204)
      (17 * (cell :: rest).length + 23) =
      PMF.pure ((VirtualCell.growLeftFinish .output before (cell :: rest) other).resumeAt 272) :=
    compile_moveLeft_boundary_eval guardedSource 3 .output (by decide) rfl before cell rest other
  rw [hEval] at hMem
  simpa [blockSize, address, guardedSource] using hMem

example (c : Configuration) (hActive : c.halted = false) :
    Step (compile guardedSource) ({ c with pc := 408 } : Configuration)
      ({ c with pc := 544 } : Configuration) :=
  compile_jump_step guardedSource 6 100 (by decide) rfl c hActive

example (c : Configuration) (hActive : c.halted = false) :
    Step (compile guardedSource) ({ c with pc := 476 } : Configuration)
      ({ c with pc := 476, halted := true } : Configuration) :=
  compile_halt_step guardedSource 7 (by decide) rfl c hActive

end Machine.Examples
