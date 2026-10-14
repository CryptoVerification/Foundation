import Foundation.Crypto.Semantics.Oracle.StraightLine
import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! Write a fixed physical field, including actual erasures, and retain its
surroundings. Existing cells are overwritten, never dropped from the tape. -/
namespace CryptoOracle.Interactive.FieldOverwrite
open Machine
set_option backward.isDefEq.respectTransparency false
def actions : List (Option Bool) → List StraightLine.Action
  | [] => []
  | cell :: rest => .write .output cell :: .right .output :: actions rest

theorem length (cells : List (Option Bool)) : (actions cells).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [actions, ih]; omega

theorem execute (cells actual before tail : List (Option Bool)) (machine : Machine.Configuration)
    (hl : cells.length = actual.length) :
    StraightLine.execute (actions cells)
      { machine with outputTape := FixedWidthCopy.frontier before (actual ++ tail) } =
      { machine with pc := machine.pc + 2 * cells.length, outputTape := FixedWidthCopy.frontier (cells.reverse ++ before) tail } := by
  induction cells generalizing actual before machine with
  | nil => cases actual <;> simp_all [actions, StraightLine.execute]
  | cons cell rest ih =>
      cases actual with
      | nil => simp at hl
      | cons old actual =>
          have ht : rest.length = actual.length := by simpa using hl
          simp only [actions, StraightLine.execute, StraightLine.apply, Machine.Configuration.updateTape,
            Machine.Configuration.advance, List.cons_append]
          have hm : ((FixedWidthCopy.frontier before (old :: (actual ++ tail))).write cell).moveRight =
              FixedWidthCopy.frontier (cell :: before) (actual ++ tail) := by
            cases actual ++ tail <;> simp [FixedWidthCopy.frontier, ResponseLoading.fromCells,
              Tape.write, Tape.moveRight]
          rw [hm]
          rw [ih actual (cell :: before) { machine with pc := machine.pc + 1 + 1 } ht]
          simp [List.reverse_cons, List.append_assoc]
          omega
end CryptoOracle.Interactive.FieldOverwrite
