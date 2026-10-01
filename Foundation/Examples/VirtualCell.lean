import Foundation.Machine.VirtualCell
import Foundation.Machine.SubroutineSimulation

namespace Machine.Examples

open Foundation.Probability

example : VirtualCell.code none = (false, false) := rfl
example : VirtualCell.code (some false) = (true, false) := rfl
example : VirtualCell.code (some true) = (true, true) := rfl
example : VirtualCell.boundary = (false, true) := rfl

example (cell : Option Bool) : VirtualCell.code cell ≠ VirtualCell.boundary :=
  VirtualCell.code_ne_boundary cell

/-- The physical input contains a logical data cell, a boundary word to its
left, and unrelated saved data on both sides. The second tape also contains
arbitrary caller data. The macro preserves every cell outside its pair. -/
def virtualCellInput : Tape :=
  { left := [some true, some false, some true],
    current := some false,
    right := [some false, some true, some false, none, some true] }

def savedCallerTape : Tape :=
  { left := [some false], current := some true, right := [some false] }

example :
    (VirtualCell.finish .input (some true) virtualCellInput savedCallerTape).inputTape =
      { left := [some true, some false, some true],
        current := some true,
        right := [some true, some true, some false, none, some true] } := rfl

example : (VirtualCell.finish .input none virtualCellInput savedCallerTape).outputTape =
    savedCallerTape := rfl

example (which : TapeId) (cell : Option Bool) (input output : Tape) :
    ((VirtualCell.finish which cell input output).tape which).left =
      ((VirtualCell.start input output).tape which).left ∧
    ((VirtualCell.finish which cell input output).tape which).right.tail =
      ((VirtualCell.start input output).tape which).right.tail :=
  VirtualCell.finish_preserves_surroundings which cell input output

example (bit : Bool) :
    RunsFor (VirtualCell.randomCell .input)
      (VirtualCell.start virtualCellInput savedCallerTape)
      (VirtualCell.finish .input (some bit) virtualCellInput savedCallerTape) 5 :=
  VirtualCell.randomCell_runs _ _ _ _

/-- A macro invocation uses the ordinary subroutine transformation. Its
return state contains the same saved data; no fresh tape is substituted. -/
example (cell : Option Bool) :
    ∃ used, used ≤ 5 ∧
      RunsFor (Program.withSubroutine [] (VirtualCell.writeCell .input cell)
        [.halt] 6) (VirtualCell.start virtualCellInput savedCallerTape)
        ((VirtualCell.finish .input cell virtualCellInput savedCallerTape).resumeAt 6)
        used := by
  simpa only [Configuration.rebasePc, List.length_nil, Nat.zero_add]
    using (VirtualCell.writeCell_runs .input cell virtualCellInput
      savedCallerTape).withSubroutine_halted [] (VirtualCell.writeCell .input cell)
        [.halt] 6 (by simp [VirtualCell.start]) rfl rfl

example : PolynomialTime (VirtualCell.writeCell .input none) :=
  VirtualCell.writeCell_polynomialTime _ _

example : PolynomialTime (VirtualCell.randomCell .output) :=
  VirtualCell.randomCell_polynomialTime _

/-- The data bit remains exactly fair after head restoration and halt, even
with arbitrary preserved prefix/suffix and a separate saved caller tape. -/
example (input output : Tape) :
    eventProb
      (evalConfigWithin (VirtualCell.randomCell .output) (VirtualCell.start input output) 5)
      (fun c => c.outputTape.right.head? = some (some true)) = 1 / 2 := by
  rw [VirtualCell.randomCell_eval]
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  have hpre :
      ((fun bit => VirtualCell.finish .output (some bit) input output) ⁻¹'
        {c : Configuration | c.outputTape.right.head? = some (some true)}) = {true} := by
    ext bit
    cases bit <;> simp [VirtualCell.finish, VirtualCell.start, VirtualCell.replacePair,
      VirtualCell.code, Configuration.updateTape]
  rw [hpre]
  simp [sampleBit, uniform]

/-- The same finite code recognizes both data values and the reserved
boundary word. The tape is unchanged; only caller control is selected. -/
example (cell : Option Bool) (before after : List (Option Bool)) (other : Tape) :
    RunsFor (VirtualCell.branchCell .input 50 60 70 80 90)
      (VirtualCell.pairStart .input (VirtualCell.code cell) before after other)
      ({ VirtualCell.pairStart .input (VirtualCell.code cell) before after other with
        pc := match cell with | none => 50 | some false => 60 | some true => 70 } :
        Configuration) 5 := by
  cases cell with
  | none =>
      exact VirtualCell.branchCell_runs .input (VirtualCell.code none)
        before after other 50 60 70 80 90
  | some bit =>
      cases bit <;>
        exact VirtualCell.branchCell_runs .input (VirtualCell.code (some _))
          before after other 50 60 70 80 90

example (before after : List (Option Bool)) (other : Tape) :
    RunsFor (VirtualCell.branchCell .output 50 60 70 80 90)
      (VirtualCell.pairStart .output VirtualCell.boundary before after other)
      ({ VirtualCell.pairStart .output VirtualCell.boundary before after other with
        pc := 80 } : Configuration) 5 :=
  VirtualCell.branchCell_runs .output VirtualCell.boundary before after other
    50 60 70 80 90

/-- The next pair already encodes logical `false`. The boundary and saved
prefix behind the old cell remain intact, and the other tape is untouched. -/
example :
    RunsFor (VirtualCell.moveRightCell .input)
      (VirtualCell.start virtualCellInput savedCallerTape)
      { pc := 3,
        inputTape :=
          { left := [some false, some false, some true, some false, some true],
            current := some true, right := [some false, none, some true] },
        outputTape := savedCallerTape,
        halted := true } 4 :=
  VirtualCell.moveRightCell_runs .input virtualCellInput savedCallerTape

/-- A single encoded cell at the right frontier has arbitrary saved caller
data behind its boundary. Moving right creates `00` with actual writes. -/
def virtualCellFrontier : Tape :=
  VirtualCell.pairTape (VirtualCell.code (some true))
    [some true, some false, some true] []

example :
    RunsFor (VirtualCell.moveRightCell .input)
      (VirtualCell.start virtualCellFrontier savedCallerTape)
      { pc := 8,
        inputTape :=
          { left := [some true, some true, some true, some false, some true],
            current := some false, right := [some false] },
        outputTape := savedCallerTape,
        halted := true } 8 :=
  VirtualCell.moveRightCell_runs .input virtualCellFrontier savedCallerTape

example :
    (VirtualCell.moveRightTape virtualCellFrontier).left.drop 2 =
      virtualCellFrontier.left :=
  VirtualCell.moveRightTape_preserves_prefix virtualCellFrontier

example (cell nextCell : Option Bool) (before after : List (Option Bool)) :
    VirtualCell.moveRightTape (VirtualCell.pairTape (VirtualCell.code cell) before
      (some (VirtualCell.code nextCell).1 :: some (VirtualCell.code nextCell).2 :: after)) =
    VirtualCell.pairTape (VirtualCell.code nextCell)
      (some (VirtualCell.code cell).2 :: some (VirtualCell.code cell).1 :: before) after :=
  VirtualCell.moveRightTape_existing _ _ _ _

example (which : TapeId) (input output : Tape) (final : Configuration)
    (run : PaddedRunsFor (VirtualCell.moveRightCell which)
      (VirtualCell.start input output) final 8) : final.halted = true :=
  VirtualCell.moveRightCell_halts_from which input output final run

example : PolynomialTime (VirtualCell.moveRightCell .input) :=
  VirtualCell.moveRightCell_polynomialTime _

/-- Inside the encoded region, left movement reaches the previous data
cell in seven real transitions, preserving the previous caller prefix. -/
example (cell previousCell : Option Bool) (before after : List (Option Bool))
    (other : Tape) :
    RunsFor (VirtualCell.moveLeftCell .output 50 80 90)
      (VirtualCell.leftStart .output (VirtualCell.code cell)
        (VirtualCell.code previousCell) before after other)
      ({ VirtualCell.pairStart .output (VirtualCell.code previousCell) before
        (some (VirtualCell.code cell).1 :: some (VirtualCell.code cell).2 :: after)
        other with pc := 50 } : Configuration) 7 := by
  cases previousCell with
  | none =>
      exact VirtualCell.moveLeftCell_runs .output (VirtualCell.code cell)
        (VirtualCell.code none) before after other 50 80 90
  | some bit =>
      cases bit <;> exact VirtualCell.moveLeftCell_runs .output (VirtualCell.code cell)
        (VirtualCell.code (some _)) before after other 50 80 90

/-- At the left boundary, the macro returns the head to the original cell
and selects the caller's growth continuation. It does not cross the guard
or pretend that insertion of a new cell has already occurred. -/
example :
    RunsFor (VirtualCell.moveLeftCell .input 50 80 90)
      (VirtualCell.start virtualCellFrontier savedCallerTape)
      ({ VirtualCell.start virtualCellFrontier savedCallerTape with pc := 80 } :
        Configuration) 9 :=
  VirtualCell.moveLeftCell_runs .input (VirtualCell.code (some true))
    VirtualCell.boundary [some true] [] savedCallerTape 50 80 90

example (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) :
    ((VirtualCell.leftFinish which current previous before after other 50 80).tape
      which).left.drop (if previous = VirtualCell.boundary then 2 else 0) = before :=
  VirtualCell.leftFinish_preserves_saved_prefix _ _ _ _ _ _ _ _

example (which : TapeId) (current previous : Bool × Bool)
    (before after : List (Option Bool)) (other : Tape) :
    evalConfigWithin (VirtualCell.moveLeftCell which 50 80 90)
      (VirtualCell.leftStart which current previous before after other)
      (VirtualCell.moveLeftSteps previous) =
      PMF.pure (VirtualCell.leftFinish which current previous before after other 50 80) :=
  VirtualCell.moveLeftCell_eval _ _ _ _ _ _ _ _ _

end Machine.Examples
