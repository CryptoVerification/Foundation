import Foundation.Crypto.Semantics.Machine.PreparationCheck

/-! An exact value-erasing simulation of physical preparation and failure
recovery. Blanks, tape positions, and phase transitions are preserved.
This is an analysis of timing, not a replacement for runtime preparation. -/
namespace Machine.PreparationShape
open Foundation.Probability TimedExecution

def cell (value : Option Bool) : Option Bool := value.map (fun _ => false)

def tape (value : Tape) : Tape :=
  ⟨value.left.map cell, cell value.current, value.right.map cell⟩

theorem tape_moveRight (value : Tape) : tape value.moveRight = (tape value).moveRight := by
  rcases value with ⟨left, current, right⟩
  cases right <;> simp [tape, Tape.moveRight, cell]

theorem tape_moveLeft (value : Tape) : tape value.moveLeft = (tape value).moveLeft := by
  rcases value with ⟨left, current, right⟩
  cases left <;> simp [tape, Tape.moveLeft, cell]

theorem tape_write (value : Tape) (bit : Bool) :
    tape (value.write (some bit)) = (tape value).write (some false) := rfl

theorem tape_fromCells (cells : List (Option Bool)) :
    tape (PairPreparation.fromCells cells) = PairPreparation.fromCells (cells.map cell) := by
  cases cells <;> simp [tape, PairPreparation.fromCells, cell]

theorem operand_shape (bits : List Bool) (tail : List (Option Bool)) :
    tape (PairPreparation.operand [] bits tail) =
      PairPreparation.fromCells (List.replicate bits.length (some false) ++ none :: tail.map cell) := by
  change tape (PairPreparation.fromCells (bits.map some ++ none :: tail)) = _
  rw [tape_fromCells]
  simp [List.map_map, cell, Function.comp_def]

def preparation : PairPreparation.Control → PairPreparation.Control
  | .reading first second buffer => .reading (tape first) (tape second) (tape buffer)
  | .checking _ first second buffer => .checking false (tape first) (tape second) (tape buffer)
  | .writingFirst _ _ first second buffer => .writingFirst false false (tape first) (tape second) (tape buffer)
  | .advancingFirst _ first second buffer => .advancingFirst false (tape first) (tape second) (tape buffer)
  | .writingSecond _ first second buffer => .writingSecond false (tape first) (tape second) (tape buffer)
  | .advancingSecond first second buffer => .advancingSecond (tape first) (tape second) (tape buffer)
  | .advancingKey first second buffer => .advancingKey (tape first) (tape second) (tape buffer)
  | .advancingMessage first second buffer => .advancingMessage (tape first) (tape second) (tape buffer)
  | .checkingEnd first second buffer => .checkingEnd (tape first) (tape second) (tape buffer)
  | .rewinding first second buffer => .rewinding (tape first) (tape second) (tape buffer)
  | .ready first second buffer => .ready (tape first) (tape second) (tape buffer)
  | .rejected first second buffer => .rejected (tape first) (tape second) (tape buffer)

theorem preparation_step (start : PairPreparation.Control) :
    PairPreparation.step (preparation start) = (PairPreparation.step start).map preparation := by
  cases start with
  | reading first second buffer =>
      cases hc : first.current <;> simp [preparation, PairPreparation.step, tape, cell, hc, PMF.pure_map]
  | checking bit first second buffer =>
      cases hc : second.current <;> simp [preparation, PairPreparation.step, tape, cell, hc, PMF.pure_map]
  | checkingEnd first second buffer =>
      cases hc : second.current <;> simp [preparation, PairPreparation.step, tape, cell, hc, PMF.pure_map]
  | rewinding first second buffer =>
      cases hf : first.left <;> cases hs : second.left <;> cases hb : buffer.left <;>
        simp [preparation, PairPreparation.step, tape, hf, hs, hb, PMF.pure_map, Tape.moveLeft]
  | writingFirst bit next first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_write]
  | advancingFirst bit first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_moveRight]
  | writingSecond bit first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_write]
  | advancingSecond first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_moveRight]
  | advancingKey first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_moveRight]
  | advancingMessage first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map, tape_moveRight]
  | ready first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map]
  | rejected first second buffer => simp [preparation, PairPreparation.step, PMF.pure_map]

def failure : PreparationFailure.Control → PreparationFailure.Control
  | .detected first second buffer => .detected (tape first) (tape second) (tape buffer)
  | .restoring phase => .restoring (preparation phase)
  | .writing first second packet => .writing (tape first) (tape second) packet
  | .returned first second response => .returned (tape first) (tape second) response

theorem failure_step (start : PreparationFailure.Control) :
    PreparationFailure.step (failure start) = (PreparationFailure.step start).map failure := by
  cases start with
  | detected first second buffer => simp [failure, preparation, PreparationFailure.step, PMF.pure_map]
  | restoring phase =>
      have hs := congrArg (fun distribution => distribution.map PreparationFailure.Control.restoring)
        (preparation_step phase)
      cases phase <;> first
        | simpa only [failure, preparation, PreparationFailure.step, PMF.map_comp, Function.comp_def] using hs
        | simp [failure, preparation, PreparationFailure.step, PMF.pure_map]
  | writing first second packet =>
      cases packet <;> simp [failure, PreparationFailure.step, PMF.map_comp, Function.comp_def, PMF.pure_map]
  | returned first second response => simp [failure, PreparationFailure.step, PMF.pure_map]

def check : PreparationCheck.Control → PreparationCheck.Control
  | .preparing phase => .preparing (preparation phase)
  | .failure phase => .failure (failure phase)

theorem check_step (start : PreparationCheck.Control) :
    PreparationCheck.step (check start) = (PreparationCheck.step start).map check := by
  cases start with
  | preparing phase =>
      have hs := congrArg (fun distribution => distribution.map PreparationCheck.Control.preparing)
        (preparation_step phase)
      cases phase <;> first
        | simpa only [check, preparation, PreparationCheck.step, PMF.map_comp, Function.comp_def] using hs
        | simp [check, preparation, failure, PreparationCheck.step, PMF.pure_map]
  | failure phase =>
      simp [check, PreparationCheck.step, failure_step, PMF.map_comp, Function.comp_def]

end Machine.PreparationShape
