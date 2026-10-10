import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration

/-! Append fixed-width fair bits on the output tape without consuming the
input tape. Unlike the marker-driven OTP sampler, width determines finite
code; no width marker is allocated on the input tape holding private data.
Existing fair-bit semantics and uniform_bits_cons supply the distribution. -/
namespace CryptoOracle.Interactive.NativeRandomAppend
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

def code : Nat → Code
  | 0 => []
  | width + 1 => [.native (.randomBit .output), .native (.moveRight .output)] ++ code width

@[simp] theorem code_length (width : Nat) : (code width).length = 2 * width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [code, ih]; omega

theorem code_native (width : Nat) :
    ∀ instruction ∈ code width, ∃ native, instruction = .native native := by
  induction width with
  | zero => simp [code]
  | succ width ih =>
      intro instruction member
      simp only [code, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl) | rest
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ih instruction rest

/-- A positive-width append overwrites an arbitrary current cell and moves
over the one explicit blank to its right during the first two instructions.
The resulting physical frame equals the blank-frontier entry, without any
host normalization. This is used after failed simulator lookups. -/
theorem overwrite_prefix {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (input : Tape)
    (past : List (Option Bool)) (width : Nat) (positive : 0 < width) (cell : Option Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ code width ++ after) oracle) 2
      (NativeCode.frame state trace { pc := before.length, inputTape := input, outputTape := { left := past, current := cell, right := [none] } }) =
    TimedExecution.eval (Reification.timedStep (before ++ code width ++ after) oracle) 2
      (NativeCode.frame state trace { pc := before.length, inputTape := input, outputTape := { left := past } }) := by
  cases width with
  | zero => omega
  | succ width =>
      simp [code, TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, NativeCode.frame, Machine.Instruction.next,
        Configuration.advance, Configuration.updateTape, Tape.write, Tape.moveRight,
        List.getElem?_append, Nat.add_assoc, PMF.bind_map]
      congr 1
      funext bit
      cases bit <;> simp

/-- The input tape and arbitrary previous output cells are physically
retained. The append operation starts and ends at a blank output frontier. -/
theorem run {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (input : Tape)
    (past : List (Option Bool)) (width : Nat) :
    TimedExecution.eval (Reification.timedStep (before ++ code width ++ after) oracle) (2 * width)
      (NativeCode.frame state trace { pc := before.length, inputTape := input, outputTape := { left := past } }) =
    (uniform (Bits width)).map (fun bits => NativeCode.frame state trace
      { pc := before.length + 2 * width, inputTape := input,
        outputTape := { left := bits.toList.reverse.map some ++ past } }) := by
  induction width generalizing before past with
  | zero => simp [TimedExecution.eval, Bits.toList, PMF.map_const, Function.const_def]
  | succ width ih =>
      rw [show 2 * (width + 1) = 2 + 2 * width by omega, TimedExecution.eval_add]
      have first : TimedExecution.eval (Reification.timedStep (before ++ code (width + 1) ++ after) oracle) 2
          (NativeCode.frame state trace { pc := before.length, inputTape := input, outputTape := { left := past } }) =
          sampleBit.bind (fun bit => PMF.pure (NativeCode.frame state trace
            { pc := before.length + 2, inputTape := input, outputTape := { left := some bit :: past } })) := by
        simp [code, TimedExecution.eval, Reification.timedStep, Reification.terminal,
          Reification.perform, Reification.action, NativeCode.frame, transition, Machine.Instruction.next,
          Configuration.advance, Configuration.updateTape, Tape.write, Tape.moveRight,
          List.getElem?_append, Nat.add_assoc, PMF.bind_map]
        congr 1
        funext bit
        cases bit <;> simp
      rw [first, PMF.bind_bind]
      simp only [PMF.pure_bind]
      have rest (bit : Bool) := ih (before ++ [.native (.randomBit .output), .native (.moveRight .output)])
        (some bit :: past)
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at rest
      simp only [code, List.append_assoc]
      simp_rw [rest]
      rw [← uniform_bits_cons]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      congr 1
      funext bit
      congr 1
      funext bits
      simp [Bits.toList, List.ofFn_succ, List.reverse_cons, List.map_append, List.append_assoc,
        Nat.add_assoc]

end CryptoOracle.Interactive.NativeRandomAppend
