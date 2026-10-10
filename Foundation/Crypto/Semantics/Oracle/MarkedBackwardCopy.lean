import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy
import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison

/-! Copy a runtime field toward the left, inserting the existing true/bit
marker pairs. The existing fixed-width copier supplies every data-bit copy;
only two ordinary marker instructions are added per bit. -/
namespace CryptoOracle.Interactive.MarkedBackwardCopy
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

private def markerActions : List StraightLine.Action :=
  [.write .input (some true), .left .input]

def cellCode (base fault : Nat) : Code :=
  FixedWidthCopy.cellCodeWith true true base fault ++ StraightLine.code markerActions

def code (base : Nat) : Nat → Nat → Code
  | 0, _ => []
  | width + 1, fault => cellCode base fault ++ code (base + 9) width fault

@[simp] theorem cellCode_length (base fault : Nat) : (cellCode base fault).length = 9 := rfl
@[simp] theorem code_length (base width fault : Nat) : (code base width fault).length = 9 * width := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih => simp [code, ih]; omega

theorem code_native (base width fault : Nat) :
    ∀ instruction ∈ code base width fault, ∃ native, instruction = .native native := by
  induction width generalizing base with
  | zero => simp [code]
  | succ width ih =>
      intro instruction member
      simp only [code, cellCode, List.mem_append] at member
      rcases member with (copy | marker) | rest
      · exact FixedWidthCopy.codeWith_native true true base 1 fault instruction (by simpa [FixedWidthCopy.codeWith] using copy)
      · simp only [StraightLine.code, markerActions, List.mem_map] at marker
        obtain ⟨action, _, rfl⟩ := marker
        exact ⟨_, rfl⟩
      · exact ih _ instruction rest

/-- The existing marker layout is compatible with concatenation. -/
theorem marked_append (first second : List Bool) :
    DelimitedTapeComparison.marked (first ++ second) =
      DelimitedTapeComparison.marked first ++ DelimitedTapeComparison.marked second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp [DelimitedTapeComparison.marked, ih]

theorem cell_run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (inputRight : List (Option Bool)) (output : Tape) (bit : Bool)
    (current : output.current = some bit) :
    TimedExecution.eval (Reification.timedStep (before ++ cellCode before.length fault ++ after) oracle) 7
      (⟨state, .running { pc := before.length, inputTape := { right := inputRight }, outputTape := output }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 9, inputTape := { right := some true :: some bit :: inputRight }, outputTape := output.moveLeft }, trace⟩ := by
  rw [show 7 = 5 + 2 by rfl, TimedExecution.eval_add]
  have h := FixedWidthCopy.backward_cell_run oracle state trace before
    (StraightLine.code markerActions ++ after) fault
    { pc := before.length, inputTape := { right := inputRight }, outputTape := output }
    bit rfl rfl current
  simp only [cellCode, List.append_assoc] at ⊢
  simp only [List.append_assoc] at h
  rw [h, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, FixedWidthCopy.cellCodeWith, StraightLine.code, StraightLine.instruction, markerActions,
    Machine.Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveLeft,
    List.getElem?_append, Nat.add_assoc]

/-- The traversed bits are supplied in reverse order. All source cells and
its arbitrary remaining prefix are preserved while the target is extended. -/
theorem run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (inputRight outputRight tail : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ code before.length bits.length fault ++ after) oracle)
      (7 * bits.length)
      (⟨state, .running { pc := before.length, inputTape := { right := inputRight }, outputTape := FixedWidthCopy.backwardFrontier outputRight (bits.map some ++ tail) }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { pc := before.length + 9 * bits.length, inputTape := { right := (DelimitedTapeComparison.marked bits.reverse).map some ++ inputRight }, outputTape := FixedWidthCopy.backwardFrontier (bits.reverse.map some ++ outputRight) tail }, trace⟩ := by
  induction bits generalizing before inputRight outputRight with
  | nil => simp [code, TimedExecution.eval, DelimitedTapeComparison.marked]
  | cons bit bits ih =>
      rw [show 7 * (bit :: bits).length = 7 + 7 * bits.length by simp; omega, TimedExecution.eval_add]
      have h := cell_run oracle state trace before (code (before.length + 9) bits.length fault ++ after)
        fault inputRight (FixedWidthCopy.backwardFrontier outputRight ((bit :: bits).map some ++ tail)) bit rfl
      simp only [code, List.length_cons, List.append_assoc] at ⊢
      simp only [List.append_assoc] at h
      rw [h, PMF.pure_bind]
      simp only [List.map_cons, List.cons_append]
      rw [FixedWidthCopy.backwardFrontier_move]
      have rest := ih (before ++ cellCode before.length fault)
        (some true :: some bit :: inputRight) (some bit :: outputRight)
      simp only [List.length_append, cellCode_length, List.append_assoc] at rest
      rw [rest]
      simp [List.reverse_cons, marked_append, DelimitedTapeComparison.marked,
        List.map_append, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

end CryptoOracle.Interactive.MarkedBackwardCopy
