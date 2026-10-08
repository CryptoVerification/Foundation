import Foundation.Crypto.Semantics.Machine.DelimitedSampler
import Foundation.Crypto.Semantics.Machine.NativeRequestGeneration
import Foundation.Crypto.Semantics.Machine.NativeAdjacentTime
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! A charged native implementation of prefix-free bitstring serialization.
The fixed request-writing code implements FiniteBitEncoding.delimit on an
explicitly delimited input. Arbitrary saved cells on both tapes are retained.
Output capacity is an entry precondition and is counted in storage bounds. -/
namespace Machine.NativeDelimitedWriter
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

private def state (pastInput pastOutput remaining : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) : Configuration :=
  { inputTape := {OneTimePad.delimitedTape remaining inputSuffix with left := pastInput.reverse.map some}
    outputTape :=
      { left := pastOutput.reverse.map some
        right := List.replicate (2 * remaining.length + 1) none ++ outputSuffix } }

private def finalState (pastInput pastOutput : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) (halted : Bool) : Configuration :=
  { pc := 14
    inputTape := {left := pastInput.reverse.map some, right := inputSuffix}
    outputTape := {left := pastOutput.reverse.map some, right := outputSuffix}
    halted := halted }

private theorem iteration (pastInput pastOutput rest : List Bool) (bit : Bool)
    (inputSuffix outputSuffix : List (Option Bool)) :
    evalConfigWithin NativeFlaggedRequest.code (state pastInput pastOutput (bit :: rest) inputSuffix outputSuffix) 8 =
      PMF.pure (state (pastInput ++ [bit]) (pastOutput ++ [true, bit]) rest inputSuffix outputSuffix) := by
  cases bit <;> cases rest <;>
    simp [state, NativeFlaggedRequest.code, evalConfigWithin, stepPMF, next, Instruction.next,
      Configuration.tape, Configuration.updateTape, Configuration.advance,
      OneTimePad.delimitedTape, Tape.write, Tape.moveRight, List.reverse_append, List.replicate_succ,
      Nat.mul_add, Nat.mul_succ, Nat.add_assoc]

private theorem run_state (pastInput pastOutput remaining : List Bool)
    (inputSuffix outputSuffix : List (Option Bool)) (halted : Bool) :
    evalConfigWithin NativeFlaggedRequest.code (state pastInput pastOutput remaining inputSuffix outputSuffix)
      (8 * remaining.length + if halted then 4 else 3) =
      PMF.pure (finalState (pastInput ++ remaining) (pastOutput ++ FiniteBitEncoding.delimit remaining)
        inputSuffix outputSuffix halted) := by
  induction remaining generalizing pastInput pastOutput with
  | nil =>
      cases halted <;>
        simp [state, finalState, NativeFlaggedRequest.code, evalConfigWithin, stepPMF, next,
          Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
          OneTimePad.delimitedTape, FiniteBitEncoding.delimit, Tape.write, Tape.moveRight, List.reverse_append]
  | cons bit rest ih =>
      rw [show 8 * (bit :: rest).length + (if halted then 4 else 3) =
        8 + (8 * rest.length + if halted then 4 else 3) by simp; omega,
        evalConfigWithin_add, iteration, PMF.pure_bind, ih]
      simp [finalState, FiniteBitEncoding.delimit, List.append_assoc]

structure Input where
  data : List Bool
  inputFrame : List (Option Bool) := []
  outputFrame : List (Option Bool) := []
  inputSuffix : List (Option Bool) := []
  outputSuffix : List (Option Bool) := []

def initial (input : Input) : Configuration :=
  (state [] [] input.data input.inputSuffix input.outputSuffix).frameLeft input.inputFrame input.outputFrame

def finish (input : Input) : Configuration :=
  (finalState input.data (FiniteBitEncoding.delimit input.data) input.inputSuffix input.outputSuffix true).frameLeft
    input.inputFrame input.outputFrame

theorem initial_eq (input : Input) : initial input =
    { inputTape := {OneTimePad.delimitedTape input.data input.inputSuffix with left := input.inputFrame}
      outputTape :=
        { left := input.outputFrame
          right := List.replicate (2 * input.data.length + 1) none ++ input.outputSuffix } } := rfl

theorem finish_input (input : Input) : (finish input).inputTape =
    {left := input.data.reverse.map some ++ input.inputFrame, right := input.inputSuffix} := rfl

theorem finish_output (input : Input) : (finish input).outputTape =
    { left := (FiniteBitEncoding.delimit input.data).reverse.map some ++ input.outputFrame
      right := input.outputSuffix } := rfl

/-- Full physical state equality includes saved context and redundant blanks. -/
theorem run (input : Input) :
    evalConfigWithin NativeFlaggedRequest.code (initial input) (8 * input.data.length + 4) = PMF.pure (finish input) := by
  unfold initial
  rw [evalConfigWithin_frameLeft NativeFlaggedRequest.code _ (by intro tape; cases tape <;> decide)]
  have h := run_state [] [] input.data input.inputSuffix input.outputSuffix true
  simp only [Bool.true_eq, ↓reduceIte, List.nil_append] at h
  rw [h, PMF.pure_map]
  rfl

theorem run_before_halt (input : Input) :
    evalConfigWithin NativeFlaggedRequest.code (initial input) (8 * input.data.length + 3) =
      PMF.pure {finish input with halted := false} := by
  unfold initial
  rw [evalConfigWithin_frameLeft NativeFlaggedRequest.code _ (by intro tape; cases tape <;> decide)]
  have h := run_state [] [] input.data input.inputSuffix input.outputSuffix false
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at h
  rw [h, PMF.pure_map]
  rfl

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed NativeFlaggedRequest.code initial (fun _ output => output)
    (fun input => PMF.pure (finish input)) (fun input => 8 * input.data.length + 4)
    (fun input => by simpa only [PMF.pure_map] using run input)
    (by decide) (fun _ => by change 0 < 15; decide) (fun _ => rfl)
    (by intro input output h; rw [PMF.mem_support_pure_iff] at h; subst output; rfl)

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input = PMF.pure (finish input, 8 * input.data.length + 4) := by
  have h := component.firstArrival_costed_of_adjacent input (8 * input.data.length + 3) (Nat.le_refl _)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin NativeFlaggedRequest.code (initial input) (8 * input.data.length + 3)).support at hState
      rw [run_before_halt, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin NativeFlaggedRequest.code (initial input) (8 * input.data.length + 4)).support at hState
      rw [run, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
  rw [timed_eval_eq] at h
  change component.firstArrival.procedure.execution.costed input =
    (evalConfigWithin NativeFlaggedRequest.code (initial input) (8 * input.data.length + 4)).map _ at h
  rw [run, PMF.pure_map] at h
  exact h

/-- The public packet decoder recovers the serialized bitstring. -/
theorem decode_packet (input : Input) (tail : List Bool) :
    FiniteBitEncoding.undelimit (FiniteBitEncoding.delimit input.data ++ tail) = some (input.data, tail) :=
  FiniteBitEncoding.undelimit_delimit _ _

end Machine.NativeDelimitedWriter
