import Foundation.Crypto.Semantics.Machine.NativeRequestGeneration
import Foundation.Crypto.Semantics.Machine.NativeExactClockSwap
import Foundation.Crypto.Semantics.Machine.TapeBitSpan

/-! Exact actual time of the balanced flagged-request writer. Both bit
values take eight transitions; saved tapes and output prefixes are retained. -/
namespace Machine.NativeFlaggedRequest
open Foundation.Probability TimedExecution
set_option maxHeartbeats 1500000

private def hasBit (state : Configuration) : Prop := ∃ bit, state.inputTape.current = some bit

private def writingPc (pc : Nat) : Prop :=
  pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨ pc = 5 ∨ pc = 6 ∨ pc = 7 ∨ pc = 8 ∨ pc = 9

private def clockValid (state : Configuration) : Prop :=
  state.halted = true ∨ state.pc = 0 ∨ (writingPc state.pc ∧ hasBit state) ∨
    state.pc = 10 ∨ state.pc = 11 ∨ state.pc = 12 ∨ state.pc = 13 ∨ state.pc = 14

private def clockRemaining (state : Configuration) : Nat :=
  if state.halted then 0 else
    match state.pc with
    | 0 => 8 * state.inputTape.bitSpan + 4
    | 1 => 8 * state.inputTape.bitSpan + 3
    | 2 => 8 * state.inputTape.bitSpan + 2
    | 3 => 8 * state.inputTape.bitSpan + 1
    | 4 => 8 * state.inputTape.bitSpan
    | 5 => 8 * state.inputTape.bitSpan + 3
    | 6 => 8 * state.inputTape.bitSpan + 2
    | 7 => 8 * state.inputTape.bitSpan + 1
    | 8 => 8 * state.inputTape.bitSpan
    | 9 => 8 * Tape.presentPrefixLength state.inputTape.right + 7
    | 10 => 8 * state.inputTape.bitSpan + 6
    | 11 => 8 * state.inputTape.bitSpan + 5
    | 12 => 3
    | 13 => 2
    | 14 => 1
    | _ => 0

noncomputable def exactClock : ExactBoundaryClock (stepPMF code) Configuration.halted where
  valid := clockValid
  remaining := clockRemaining
  terminal := by
    intro state hValid
    cases hHalt : state.halted with
    | true => simp [clockRemaining, hHalt]
    | false =>
        rcases hValid with h | hPc | ⟨hPc, bit, hBit⟩ | hPc | hPc | hPc | hPc | hPc
        · simp_all
        · simp [clockRemaining, hHalt, hPc]
        · rcases hPc with hPc | hPc | hPc | hPc | hPc | hPc | hPc | hPc | hPc
          all_goals simp [clockRemaining, hHalt, hPc, Tape.bitSpan_some _ _ hBit]
        all_goals simp [clockRemaining, hHalt, hPc]
  transition := by
    intro state hValid hActive target hTarget
    rcases hValid with hHalt | hPc | ⟨hPc, bit, hCurrent⟩ | hPc | hPc | hPc | hPc | hPc
    · simp_all
    · cases hCurrent : state.inputTape.current with
      | none =>
          have hEq : target = {state with pc := 12} := by
            simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; right; right; left; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent]
      | some bit =>
          cases bit with
          | false =>
              have hEq : target = {state with pc := 1} := by
                simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
              subst target
              constructor
              · simp [clockValid, writingPc, hasBit, hCurrent]
              · simp [clockRemaining, hActive, hPc]
          | true =>
              have hEq : target = {state with pc := 5} := by
                simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
              subst target
              constructor
              · simp [clockValid, writingPc, hasBit, hCurrent]
              · simp [clockRemaining, hActive, hPc]
    · rcases hPc with hPc | hPc | hPc | hPc | hPc | hPc | hPc | hPc | hPc
      · have hEq : target = (state.updateTape .output (fun tape => tape.write (some true))).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = (state.updateTape .output Tape.moveRight).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = (state.updateTape .output (fun tape => tape.write (some false))).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = {state with pc := 9} := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]; omega
      · have hEq : target = (state.updateTape .output (fun tape => tape.write (some true))).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = (state.updateTape .output Tape.moveRight).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = (state.updateTape .output (fun tape => tape.write (some true))).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
      · have hEq : target = {state with pc := 9} := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]; omega
      · have hEq : target = (state.updateTape .input Tape.moveRight).advance := by
          simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
        subst target
        constructor
        · simp [clockValid, writingPc, hasBit, Configuration.advance, Configuration.updateTape, hPc, hCurrent]
        · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc, hCurrent]
    · have hEq : target = (state.updateTape .output Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · simp [clockValid, Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]
    · have hEq : target = {state with pc := 0} := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · simp [clockValid, Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]
    · have hEq : target = (state.updateTape .output (fun tape => tape.write (some false))).advance := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · simp [clockValid, Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]
    · have hEq : target = (state.updateTape .output Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · simp [clockValid, Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]
    · have hEq : target = {state with halted := true} := by
        simpa [stepPMF, Machine.next, code, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · simp [clockValid, Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, Configuration.advance, Configuration.updateTape, hActive, hPc]

theorem initial_clock_valid (input : NativeBitstringContext) : exactClock.valid (initial input) := by
  right; left; rfl

theorem initial_clock (input : NativeBitstringContext) :
    exactClock.remaining (initial input) = 8 * input.data.length + 4 := by
  simp [exactClock, clockRemaining, initial, OneTimePad.state]

theorem firstArrival_joint (input : NativeBitstringContext) :
    component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 8 * input.data.length + 4) := by
  have h := component.firstArrival_joint_of_clock exactClock input (initial_clock_valid input)
    (by change exactClock.remaining (initial input) ≤ 8 * input.data.length + 4; rw [initial_clock])
  rw [PMF.map_comp] at h
  change component.firstArrival.procedure.execution.costed input =
    (PMF.pure (finish input)).map (fun state => (state, exactClock.remaining (initial input))) at h
  rw [initial_clock, PMF.pure_map] at h
  exact h

theorem firstArrival_time_distribution (input : NativeBitstringContext) :
    (component.firstArrival.procedure.execution.costed input).map Prod.snd =
      PMF.pure (8 * input.data.length + 4) := by
  rw [firstArrival_joint, PMF.pure_map]

end Machine.NativeFlaggedRequest
