import Foundation.Crypto.Semantics.Machine.NativeBitstringRewind
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeExactClockSwap
import Foundation.Crypto.Semantics.Machine.NativeTraceTime

/-! An exact native clock for contextual rewind. Arbitrary saved data on
the other tape and to the right are allowed; only the traversed left block
must contain bits. Each branch consumes the same number of transitions. -/
namespace Machine.NativeBitstringRewind
open Foundation.Probability TimedExecution
set_option maxHeartbeats 800000

private def clockValid (state : Configuration) : Prop :=
  state.halted = true ∨
    (state.pc = 0 ∧ ∃ bits : List Bool, state.inputTape.left = bits.map some) ∨
    (state.pc = 1 ∧ ∃ bits : List Bool, state.inputTape.left = bits.map some ∧
      (state.inputTape.current = none → bits = [])) ∨
    state.pc = 2 ∨ state.pc = 3

private def clockRemaining (state : Configuration) : Nat :=
  if state.halted then 0 else
    match state.pc with
    | 0 => 2 * state.inputTape.left.length + 4
    | 1 => if state.inputTape.current = none then 3 else 2 * state.inputTape.left.length + 5
    | 2 => 2
    | 3 => 1
    | _ => 0

noncomputable def exactClock : ExactBoundaryClock (stepPMF rewindBitstring) Configuration.halted where
  valid := clockValid
  remaining := clockRemaining
  terminal := by
    intro state hValid
    cases hHalt : state.halted with
    | true => simp [clockRemaining, hHalt]
    | false =>
        rcases hValid with h | ⟨hPc, _⟩ | ⟨hPc, _⟩ | hPc | hPc
        · simp_all
        all_goals simp [clockRemaining, hHalt, hPc]
        all_goals split <;> omega
  transition := by
    intro state hValid hActive target hTarget
    rcases hValid with hHalt | ⟨hPc, bits, hLeft⟩ | ⟨hPc, bits, hLeft, hBlank⟩ | hPc | hPc
    · simp_all
    · have hEq : target = (state.updateTape .input Tape.moveLeft).advance := by
        simpa [stepPMF, Machine.next, rewindBitstring, hActive, hPc, Instruction.next] using hTarget
      subst target
      cases bits with
      | nil =>
          constructor
          · right; right; left
            exact ⟨by simp [Configuration.advance, Configuration.updateTape, hPc], [], by simp [Configuration.advance, Configuration.updateTape, Tape.moveLeft, hLeft], by simp⟩
          · simp [clockRemaining, Configuration.advance, Configuration.updateTape, Tape.moveLeft, hLeft, hActive, hPc]
      | cons bit rest =>
          constructor
          · right; right; left
            exact ⟨by simp [Configuration.advance, Configuration.updateTape, hPc], rest,
              by simp [Configuration.advance, Configuration.updateTape, Tape.moveLeft, hLeft],
              by simp [Configuration.advance, Configuration.updateTape, Tape.moveLeft, hLeft]⟩
          · simp [clockRemaining, Configuration.advance, Configuration.updateTape, Tape.moveLeft, hLeft, hActive, hPc]
            omega
    · cases hCurrent : state.inputTape.current with
      | none =>
          have hEq : target = {state with pc := 2} := by
            simpa [stepPMF, Machine.next, rewindBitstring, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; left; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent]
      | some bit =>
          have hEq : target = {state with pc := 0} := by
            cases bit <;>
              simpa [stepPMF, Machine.next, rewindBitstring, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; left; exact ⟨rfl, bits, hLeft⟩
          · simp [clockRemaining, hActive, hPc, hCurrent]
    · have hEq : target = (state.updateTape .input Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, rewindBitstring, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; right; simp [Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]
    · have hEq : target = {state with halted := true} := by
        simpa [stepPMF, Machine.next, rewindBitstring, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · left; rfl
      · simp [clockRemaining, hActive, hPc]

theorem initial_clock_valid (input : Input) : exactClock.valid (initial input) := by
  right; left
  exact ⟨rfl, input.bits.reverse, rfl⟩

theorem initial_clock (input : Input) : exactClock.remaining (initial input) = 2 * input.bits.length + 4 := by
  simp [exactClock, clockRemaining, initial]

theorem firstArrival_fixed_time (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (component.firstArrival.procedure.execution.costed input).support) :
    result.2 = 2 * input.bits.length + 4 := by
  rw [component.firstArrival_costed] at hResult
  have h := exactClock.fixed_time (2 * input.bits.length + 4) (initial input)
    (initial_clock_valid input) (by rw [initial_clock]) result hResult
  rwa [initial_clock] at h

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 2 * input.bits.length + 4) := by
  exact component.firstArrival_costed_of_trace input (finish input) (2 * input.bits.length + 4)
    (rewindBitstring_runs_from input.bits input.current input.right input.other)
    rewindBitstring_no_randomBit rfl (Nat.le_refl _)

theorem firstArrival_time_distribution (input : Input) :
    (component.firstArrival.procedure.execution.costed input).map Prod.snd =
      PMF.pure (2 * input.bits.length + 4) := by
  rw [firstArrival_joint, PMF.pure_map]

theorem output_firstArrival_joint (input : Input) :
    outputComponent.firstArrival.procedure.execution.costed input =
      PMF.pure ((finish input).swapTapes, 2 * input.bits.length + 4) := by
  have hValid : (swapTapesExactClock exactClock).valid (outputComponent.procedure.execution.entry input) :=
    initial_clock_valid input
  have hBound : (swapTapesExactClock exactClock).remaining (outputComponent.procedure.execution.entry input) ≤
      outputComponent.procedure.execution.budget input := by
    change (swapTapesExactClock exactClock).remaining (initial input).swapTapes ≤ 2 * input.bits.length + 4
    rw [swapTapesExactClock_remaining, initial_clock]
  have h := outputComponent.firstArrival_joint_of_clock (swapTapesExactClock exactClock) input hValid hBound
  rw [PMF.map_comp] at h
  change outputComponent.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state.swapTapes,
      (swapTapesExactClock exactClock).remaining (initial input).swapTapes)) at h
  rw [swapTapesExactClock_remaining, initial_clock, PMF.pure_map] at h
  exact h

end Machine.NativeBitstringRewind
