import Foundation.Crypto.Semantics.Machine.NativeForwardErasure
import Foundation.Crypto.Semantics.Machine.NativeExactClockSwap

/-! Exact actual time of a forward erasure scan. Saved data before and
after the first delimiter and the other tape do not affect the clock. -/
namespace Machine.NativeForwardErasure
open Foundation.Probability TimedExecution
set_option maxHeartbeats 800000

private def leadingBits : List (Option Bool) → Nat
  | [] => 0
  | none :: _ => 0
  | some _ :: rest => leadingBits rest + 1

private def clockValid (state : Configuration) : Prop :=
  state.halted = true ∨ state.pc = 0 ∨
    (state.pc = 1 ∧ ∃ bit, state.inputTape.current = some bit) ∨
    state.pc = 2 ∨ state.pc = 3 ∨ state.pc = 4

private def clockRemaining (state : Configuration) : Nat :=
  if state.halted then 0 else
    match state.pc with
    | 0 => 4 * leadingBits (state.inputTape.current :: state.inputTape.right) + 2
    | 1 => 4 * leadingBits (state.inputTape.current :: state.inputTape.right) + 1
    | 2 => 4 * leadingBits state.inputTape.right + 4
    | 3 => 4 * leadingBits (state.inputTape.current :: state.inputTape.right) + 3
    | 4 => 1
    | _ => 0

noncomputable def exactClock : ExactBoundaryClock (stepPMF code) Configuration.halted where
  valid := clockValid
  remaining := clockRemaining
  terminal := by
    intro state hValid
    cases hHalt : state.halted with
    | true => simp [clockRemaining, hHalt]
    | false =>
        rcases hValid with h | hPc | ⟨hPc, _⟩ | hPc | hPc | hPc
        · simp_all
        all_goals simp [clockRemaining, hHalt, hPc]
  transition := by
    intro state hValid hActive target hTarget
    rcases hValid with hHalt | hPc | ⟨hPc, bit, hCurrent⟩ | hPc | hPc | hPc
    · simp_all
    · cases hCurrent : state.inputTape.current with
      | none =>
          have hEq : target = {state with pc := 4} := by
            simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; right; right; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent, leadingBits]
      | some bit =>
          have hEq : target = {state with pc := 1} := by
            cases bit <;>
              simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; left; exact ⟨rfl, bit, hCurrent⟩
          · simp [clockRemaining, hActive, hPc, hCurrent, leadingBits]
    · have hEq : target = (state.updateTape .input (fun tape => tape.write none)).advance := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, hActive, hPc, hCurrent, leadingBits, Configuration.advance, Configuration.updateTape, Tape.write]
        omega
    · have hEq : target = (state.updateTape .input Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · cases hRight : state.inputTape.right <;>
          simp [clockRemaining, hActive, hPc, hRight, leadingBits, Configuration.advance, Configuration.updateTape, Tape.moveRight]
    · have hEq : target = {state with pc := 0} := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; left; rfl
      · simp [clockRemaining, hActive, hPc]
    · have hEq : target = {state with halted := true} := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · left; rfl
      · simp [clockRemaining, hActive, hPc]

private theorem leadingBits_block (bits : List Bool) (after : List (Option Bool)) :
    leadingBits (bits.map some ++ none :: after) = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [leadingBits, ih]

theorem initial_clock_valid (input : Input) : exactClock.valid (initial input) := by
  right; left; rfl

theorem initial_clock (input : Input) : exactClock.remaining (initial input) = 4 * input.bits.length + 2 := by
  cases hBits : input.bits <;>
    simp [exactClock, clockRemaining, initial, hBits, leadingBits, leadingBits_block]

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 4 * input.bits.length + 2) := by
  have h := component.firstArrival_joint_of_clock exactClock input (initial_clock_valid input)
    (by change exactClock.remaining (initial input) ≤ 4 * input.bits.length + 2; rw [initial_clock])
  rw [PMF.map_comp] at h
  change component.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state, exactClock.remaining (initial input))) at h
  rw [initial_clock, PMF.pure_map] at h
  exact h

theorem output_firstArrival_joint (input : Input) :
    outputComponent.firstArrival.procedure.execution.costed input =
      PMF.pure ((finish input).swapTapes, 4 * input.bits.length + 2) := by
  have hValid : (swapTapesExactClock exactClock).valid (outputComponent.procedure.execution.entry input) :=
    initial_clock_valid input
  have hBound : (swapTapesExactClock exactClock).remaining (outputComponent.procedure.execution.entry input) ≤
      outputComponent.procedure.execution.budget input := by
    change (swapTapesExactClock exactClock).remaining (initial input).swapTapes ≤ 4 * input.bits.length + 2
    rw [swapTapesExactClock_remaining, initial_clock]
  have h := outputComponent.firstArrival_joint_of_clock (swapTapesExactClock exactClock) input hValid hBound
  rw [PMF.map_comp] at h
  change outputComponent.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state.swapTapes,
      (swapTapesExactClock exactClock).remaining (initial input).swapTapes)) at h
  rw [swapTapesExactClock_remaining, initial_clock, PMF.pure_map] at h
  exact h

end Machine.NativeForwardErasure
