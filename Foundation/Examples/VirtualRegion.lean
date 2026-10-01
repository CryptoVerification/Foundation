import Foundation.Machine.VirtualRegion
import Foundation.Machine.SubroutineSimulation
import Foundation.Examples.VirtualCell

namespace Machine.Examples

/-- The finite wrapper contains only existing one-bit instructions. -/
example (which : TapeId) : (VirtualCell.growLeftCell which).length = 50 := rfl

/-- Logical blanks inside a region are encoded as ordinary physical `00`
pairs. They do not truncate the right-frontier scan. -/
def guardedLogicalCells : List (Option Bool) := [some true, none, some false]

def guardedSavedPrefix : List (Option Bool) := [some true, none, some false, some true]

example :
    RunsFor (VirtualCell.growLeftCell .input)
      (VirtualCell.growLeftStart .input guardedSavedPrefix guardedLogicalCells
        savedCallerTape)
      (VirtualCell.growLeftFinish .input guardedSavedPrefix guardedLogicalCells
        savedCallerTape) 65 :=
  VirtualCell.growLeftCell_runs .input guardedSavedPrefix guardedLogicalCells savedCallerTape

/-- The boundary and caller prefix remain exactly where they were. The new
blank precedes all three old logical cells, in their original order. -/
example :
    (VirtualCell.growLeftFinish .input guardedSavedPrefix guardedLogicalCells
      savedCallerTape).inputTape =
      { left := [some true, some false, some true, none, some false, some true],
        current := some false,
        right := [some false, some true, some true, some false, some false,
          some true, some false] } := rfl

example :
    (VirtualCell.growLeftFinish .input guardedSavedPrefix guardedLogicalCells
      savedCallerTape).outputTape = savedCallerTape :=
  VirtualCell.growLeftFinish_preserves_other_tape .input guardedSavedPrefix
    guardedLogicalCells savedCallerTape

/-- An empty, already guarded region is materialized by fourteen charged
transitions. The guard is a caller precondition; the new pair is written
by the machine and is not supplied as a free state replacement. -/
example (before : List (Option Bool)) (other : Tape) :
    RunsFor (VirtualCell.growLeftCell .output)
      (VirtualCell.growLeftStart .output before [] other)
      (VirtualCell.growLeftFinish .output before [] other) 14 :=
  VirtualCell.growLeftCell_runs .output before [] other

example (which : TapeId) (before cells : List (Option Bool)) (other : Tape)
    (final : Configuration)
    (run : PaddedRunsFor (VirtualCell.growLeftCell which)
      (VirtualCell.growLeftStart which before cells other) final (17 * cells.length + 14)) :
    final.halted = true :=
  VirtualCell.growLeftCell_halts which before cells other final run

/-- The macro can return to ordinary caller code while retaining these
same tapes. Invocation uses the proved operational subroutine construction. -/
example (which : TapeId) (before cells : List (Option Bool)) (other : Tape) :
    ∃ used, used ≤ 17 * cells.length + 14 ∧
      RunsFor (Program.withSubroutine [] (VirtualCell.growLeftCell which) [.halt] 51)
        (VirtualCell.growLeftStart which before cells other)
        ((VirtualCell.growLeftFinish which before cells other).resumeAt 51) used := by
  simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
    using (VirtualCell.growLeftCell_runs which before cells other).withSubroutine_halted
      [] (VirtualCell.growLeftCell which) [.halt] 51
        (by cases which <;> change 0 ≤ 50 <;> omega)
        (by cases which <;> rfl) rfl

example : PolynomiallyBounded (fun m => 17 * m + 14) :=
  VirtualCell.growLeftCell_bound_polynomiallyBounded

example (which : TapeId) (before cells : List (Option Bool)) (other : Tape) :
    ((VirtualCell.growLeftFinish which before cells other).tape which).cells ≤
      ((VirtualCell.growLeftStart which before cells other).tape which).cells + 2 :=
  VirtualCell.growLeftFinish_storage_le _ _ _ _

end Machine.Examples
