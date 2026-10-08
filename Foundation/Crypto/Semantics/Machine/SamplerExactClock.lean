import Foundation.Crypto.Semantics.Machine.NativeRequestGeneration
import Foundation.Crypto.Semantics.Machine.NativeExactClockSwap
import Foundation.Crypto.Semantics.Machine.TapeBitSpan

/-! Exact actual cost of contextual fair-bit sampling. The sampled values
are not read by the clock. Every random successor consumes one real step. -/
namespace Machine.NativeContextualSampler
open Foundation.Probability TimedExecution
set_option maxHeartbeats 1000000

private def hasBit (state : Configuration) : Prop := ∃ bit, state.inputTape.current = some bit

private def clockValid (state : Configuration) : Prop :=
  state.halted = true ∨ state.pc = 0 ∨ (state.pc = 1 ∧ hasBit state) ∨
    (state.pc = 2 ∧ hasBit state) ∨ state.pc = 3 ∨ state.pc = 4 ∨ state.pc = 5

private def clockRemaining (state : Configuration) : Nat :=
  if state.halted then 0 else
    match state.pc with
    | 0 => 5 * state.inputTape.bitSpan + 2
    | 1 => 5 * state.inputTape.bitSpan + 1
    | 2 => 5 * state.inputTape.bitSpan
    | 3 => 5 * state.inputTape.bitSpan + 4
    | 4 => 5 * state.inputTape.bitSpan + 3
    | 5 => 1
    | _ => 0

noncomputable def exactClock : ExactBoundaryClock (stepPMF OneTimePad.keygen) Configuration.halted where
  valid := clockValid
  remaining := clockRemaining
  terminal := by
    intro state hValid
    cases hHalt : state.halted with
    | true => simp [clockRemaining, hHalt]
    | false =>
        rcases hValid with h | hPc | ⟨hPc, hBit⟩ | ⟨hPc, bit, hBit⟩ | hPc | hPc | hPc
        · simp_all
        all_goals try simp [clockRemaining, hHalt, hPc]
        simp [Tape.bitSpan_some _ _ hBit]
  transition := by
    intro state hValid hActive target hTarget
    rcases hValid with hHalt | hPc | ⟨hPc, hBit⟩ | ⟨hPc, bit, hCurrent⟩ | hPc | hPc | hPc
    · simp_all
    · cases hCurrent : state.inputTape.current with
      | none =>
          have hEq : target = {state with pc := 5} := by
            simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; right; right; right; right; rfl
          · simp [clockRemaining, hActive, hPc, hCurrent]
      | some bit =>
          have hEq : target = {state with pc := 1} := by
            cases bit <;> simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next, Configuration.tape, hCurrent] using hTarget
          subst target
          constructor
          · right; right; left; exact ⟨rfl, bit, hCurrent⟩
          · simp [clockRemaining, hActive, hPc]
    · have hDraw : stepPMF OneTimePad.keygen state = sampleBit.map (fun bit =>
          (state.updateTape .output (fun tape => tape.write (some bit))).advance) := by
        simp [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next]
        congr 1
        funext bit
        cases bit <;> rfl
      rw [hDraw, PMF.mem_support_map_iff] at hTarget
      obtain ⟨draw, _, rfl⟩ := hTarget
      constructor
      · right; right; right; left
        exact ⟨by simp [Configuration.advance, Configuration.updateTape, hPc], hBit⟩
      · simp [clockRemaining, hActive, hPc, Configuration.advance, Configuration.updateTape]
    · have hEq : target = (state.updateTape .input Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, hActive, hPc, hCurrent, Configuration.advance, Configuration.updateTape]
        omega
    · have hEq : target = (state.updateTape .output Tape.moveRight).advance := by
        simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; right; right; right; right; left; simp [Configuration.advance, Configuration.updateTape, hPc]
      · simp [clockRemaining, hActive, hPc, Configuration.advance, Configuration.updateTape]
    · have hEq : target = {state with pc := 0} := by
        simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · right; left; rfl
      · simp [clockRemaining, hActive, hPc]
    · have hEq : target = {state with halted := true} := by
        simpa [stepPMF, Machine.next, OneTimePad.keygen, hActive, hPc, Instruction.next] using hTarget
      subst target
      constructor
      · left; rfl
      · simp [clockRemaining, hActive, hPc]

theorem initial_clock_valid (input : NativeBitstringContext) : exactClock.valid (initial input) := by
  right; left; rfl

theorem initial_clock (input : NativeBitstringContext) :
    exactClock.remaining (initial input) = 5 * input.data.length + 2 := by
  simp [exactClock, clockRemaining, initial, OneTimePad.state]

theorem firstArrival_joint (input : NativeBitstringContext) :
    component.firstArrival.procedure.execution.costed input =
      ((uniform (Foundation.Symmetric.Bits input.data.length)).map (finish input)).map
        (fun state => (state, 5 * input.data.length + 2)) := by
  have h := component.firstArrival_joint_of_clock exactClock input (initial_clock_valid input)
    (by change exactClock.remaining (initial input) ≤ 5 * input.data.length + 2; rw [initial_clock])
  rw [PMF.map_comp] at h
  change component.firstArrival.procedure.execution.costed input =
    ((uniform (Foundation.Symmetric.Bits input.data.length)).map (finish input)).map
      (fun state => (state, exactClock.remaining (initial input))) at h
  rwa [initial_clock] at h

theorem firstArrival_key_time (input : NativeBitstringContext) :
    (component.firstArrival.procedure.execution.costed input).map (fun result => (readKey input result.1, result.2)) =
      (uniform (Foundation.Symmetric.Bits input.data.length)).map (fun key => (key, 5 * input.data.length + 2)) := by
  rw [firstArrival_joint, PMF.map_comp, PMF.map_comp]
  simp only [Function.comp_def, readKey_finish]

theorem firstArrival_time_distribution (input : NativeBitstringContext) :
    (component.firstArrival.procedure.execution.costed input).map Prod.snd =
      PMF.pure (5 * input.data.length + 2) := by
  rw [firstArrival_joint, PMF.map_comp, PMF.map_comp]
  exact PMF.map_const _ _

theorem equivalentEntries_firstArrival_key_time (input : NativeComponent.EquivalentInput component) :
    (component.equivalentEntries.firstArrival.procedure.execution.costed input).map
      (fun result => (readKey input.logical result.1, result.2)) =
    (uniform (Foundation.Symmetric.Bits input.logical.data.length)).map
      (fun key => (key, 5 * input.logical.data.length + 2)) := by
  rw [component.equivalentEntries_firstArrival_observe input (readKey input.logical)
    (fun first second h => readKey_equivalent input.logical first second h)]
  exact firstArrival_key_time input.logical

end Machine.NativeContextualSampler
