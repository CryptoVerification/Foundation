import Foundation.Crypto.Semantics.Machine.NativeBackwardErasure
import Foundation.Crypto.Semantics.Machine.NativeExactClockSwap

/-! Exact actual time of a backward erasure scan. Saved data before and
beyond the preceding delimiter and the other tape do not affect the clock. -/
namespace Machine.NativeBackwardErasure
open Foundation.Probability TimedExecution
set_option maxHeartbeats 800000

private def leadingBits : List (Option Bool) → Nat
  | [] => 0
  | none :: _ => 0
  | some _ :: rest => leadingBits rest + 1

private def clockValid (state : Configuration) : Prop :=
  state.halted = true ∨ state.pc = 0 ∨ state.pc = 1 ∨ state.pc = 2 ∨ state.pc = 3 ∨ state.pc = 4

private def clockRemaining (state : Configuration) : Nat :=
  if state.halted then 0 else
    match state.pc with
    | 0 => 4 * leadingBits state.outputTape.left + 3
    | 1 => if state.outputTape.current = none then 2 else 4 * leadingBits state.outputTape.left + 6
    | 2 => 4 * leadingBits state.outputTape.left + 5
    | 3 => 4 * leadingBits state.outputTape.left + 4
    | 4 => 1
    | _ => 0

noncomputable def exactClock : ExactBoundaryClock (stepPMF eraseOutputBlock) Configuration.halted where
  valid := clockValid
  remaining := clockRemaining
  terminal := by
    intro state hValid
    cases hHalt : state.halted with
    | true => simp [clockRemaining, hHalt]
    | false =>
        rcases hValid with h | hPc | hPc | hPc | hPc | hPc
        · simp_all
        all_goals simp [clockRemaining, hHalt, hPc]
        all_goals split <;> omega
  transition := by
    intro state hValid hActive target hTarget
    rcases hValid with hHalt | hPc | hPc | hPc | hPc | hPc
    · simp_all
    · have hEq : target = (state.updateTape .output Tape.moveLeft).advance := by
        simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · cases hLeft : state.outputTape.left with
        | nil => simp [clockRemaining, hActive, hPc, hLeft, leadingBits, Configuration.advance, Configuration.updateTape, Tape.moveLeft]
        | cons cell rest =>
            cases cell <;>
              simp [clockRemaining, hActive, hPc, hLeft, leadingBits, Configuration.advance, Configuration.updateTape, Tape.moveLeft]
            omega
    · cases hCurrent : state.outputTape.current with
      | none =>
          have hEq : target = {state with pc := 4} := by
            simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; right; right; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent]
      | some bit =>
          have hEq : target = {state with pc := 2} := by
            cases bit <;>
              simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; left; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent]
    · have hEq : target = (state.updateTape .output (fun tape => tape.write none)).advance := by
        simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, hActive, hPc, Configuration.advance, Configuration.updateTape, Tape.write]
    · have hEq : target = {state with pc := 0} := by
        simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; left; rfl
      · simp [clockRemaining, hActive, hPc]
    · have hEq : target = {state with halted := true} := by
        simpa [stepPMF, Machine.next, eraseOutputBlock, hActive, hPc, Instruction.next] using hTarget
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

theorem initial_clock (input : Input) : exactClock.remaining (initial input) = 4 * input.bits.length + 3 := by
  change 4 * leadingBits (input.bits.reverse.map some ++ none :: input.before) + 3 = _
  rw [leadingBits_block, List.length_reverse]

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 4 * input.bits.length + 3) := by
  have h := component.firstArrival_joint_of_clock exactClock input (initial_clock_valid input)
    (by change exactClock.remaining (initial input) ≤ 4 * input.bits.length + 3; rw [initial_clock])
  rw [PMF.map_comp] at h
  change component.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state, exactClock.remaining (initial input))) at h
  rw [initial_clock, PMF.pure_map] at h
  exact h

theorem input_firstArrival_joint (input : Input) :
    inputComponent.firstArrival.procedure.execution.costed input =
      PMF.pure ((finish input).swapTapes, 4 * input.bits.length + 3) := by
  have hValid : (swapTapesExactClock exactClock).valid (inputComponent.procedure.execution.entry input) :=
    initial_clock_valid input
  have hBound : (swapTapesExactClock exactClock).remaining (inputComponent.procedure.execution.entry input) ≤
      inputComponent.procedure.execution.budget input := by
    change (swapTapesExactClock exactClock).remaining (initial input).swapTapes ≤ 4 * input.bits.length + 3
    rw [swapTapesExactClock_remaining, initial_clock]
  have h := inputComponent.firstArrival_joint_of_clock (swapTapesExactClock exactClock) input hValid hBound
  rw [PMF.map_comp] at h
  change inputComponent.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state.swapTapes,
      (swapTapesExactClock exactClock).remaining (initial input).swapTapes)) at h
  rw [swapTapesExactClock_remaining, initial_clock, PMF.pure_map] at h
  exact h

end Machine.NativeBackwardErasure
