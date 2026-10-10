import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! Move from the cell immediately before a runtime key to the response
following it, erasing the last key cell to reserve an actual blank boundary.
The stored input table is untouched. The erased source-key cell is explicit;
this routine does not claim to preserve that redundant output copy. -/
namespace CryptoOracle.Interactive.NativePacketSuffix
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def actions (keyWidth : Nat) : List StraightLine.Action :=
  List.replicate keyWidth (.right .output) ++ [.write .output none, .right .output]

@[simp] theorem actions_length (keyWidth : Nat) : (actions keyWidth).length = keyWidth + 2 := by
  simp [actions]

/-- A scan past the left tape boundary represents one outer blank. -/
def restoredBefore (before : List (Option Bool)) : List (Option Bool) := before.headD none :: before.tail

private theorem frontier_right (right before : List (Option Bool)) :
    (FixedWidthCopy.backwardFrontier right before).moveRight =
      FixedWidthCopy.frontier (restoredBefore before) right := by
  cases before <;> cases right <;> rfl

/-- Every head move and the separator write is executed. Only the last
runtime key bit is erased; all input cells and older output cells survive. -/
theorem execute (pc : Nat) (input : Tape) (before : List (Option Bool))
    (keyPrefix packet : List Bool) (last : Bool) :
    StraightLine.execute (actions (keyPrefix.length + 1))
      { pc := pc, inputTape := input,
        outputTape := FixedWidthCopy.backwardFrontier
          ((keyPrefix ++ [last] ++ packet).map some ++ [none]) before } =
      ({ pc := pc + (keyPrefix.length + 1) + 2, inputTape := input,
         outputTape := FixedWidthCopy.frontier
           (none :: keyPrefix.reverse.map some ++ restoredBefore before) (packet.map some ++ [none]) } : Machine.Configuration) := by
  simp only [actions, List.replicate_succ, List.cons_append, StraightLine.execute,
    StraightLine.apply, Configuration.updateTape, Configuration.advance, frontier_right]
  have traverse := FixedWidthCopy.advance_output keyPrefix (restoredBefore before)
    (some last :: packet.map some ++ [none]) ({ pc := pc + 1, inputTape := input } : Machine.Configuration)
  simp only [List.map_append, List.map_cons, List.append_assoc, List.nil_append, List.cons_append] at ⊢
  rw [StraightLine.execute_append]
  simp only [List.cons_append] at traverse ⊢
  rw [traverse]
  simp [StraightLine.execute, StraightLine.apply, Configuration.updateTape, Configuration.advance,
    FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.write, Tape.moveRight, Nat.add_assoc]
  constructor
  · omega
  · cases packet <;> rfl

end CryptoOracle.Interactive.NativePacketSuffix
