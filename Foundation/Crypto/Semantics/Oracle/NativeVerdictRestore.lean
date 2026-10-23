import Foundation.Crypto.Semantics.Oracle.NativeHaltReturnChecked
import Foundation.Examples.MixedCircuitMACAnalysisNative

/-! Materialize verdict bits, then restore the original verdict head using
real one-cell moves. The output region is overwritten explicitly; no tape
reset or hidden-state serialization is part of this contract. -/
namespace CryptoOracle.Interactive.NativeVerdictRestore
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def rewind (count : Nat) : Code := List.replicate count (.native (.moveLeft .output)) ++ [.native .halt]

def code (mask : List Bool) : Code := HaltReturn.host (NativeVerdictPacket.code mask) (rewind mask.length)

def restored (output : Tape) (bits : List Bool) : Tape :=
  (Tape.moveLeft^[bits.length]) (NativeVerdictPacket.written output bits)

def finish (mask : List Bool) (input output : Tape) : Machine.Configuration :=
  {pc := (NativeVerdictPacket.code mask).length + mask.length, inputTape := input,
    outputTape := restored output (NativeVerdictPacket.result mask (output.current.getD false)), halted := true}

theorem code_length (mask : List Bool) : (code mask).length = 5 * mask.length + 5 := by
  simp [code, HaltReturn.host_length, NativeVerdictPacket.code_length, rewind]; omega

private theorem moves_run (program : Code) (base count : Nat) (input output : Tape)
    (located : ∀ index, index < count → program[base + index]? = some (.native (.moveLeft .output))) :
    NativeDeterministic.run program count (NativeVerdictPacket.start base input output) =
      some (NativeVerdictPacket.start (base + count) input ((Tape.moveLeft^[count]) output)) := by
  induction count generalizing base output with
  | zero => simp [NativeDeterministic.run]
  | succ count ih =>
    have first : program[base]? = some (.native (.moveLeft .output)) := by simpa using located 0 (by omega)
    have next : ∀ index, index < count → program[base + 1 + index]? = some (.native (.moveLeft .output)) := by
      intro index inside
      simpa only [Nat.add_assoc, Nat.add_comm 1] using located (index + 1) (by omega)
    simp only [NativeDeterministic.run, NativeDeterministic.next?, NativeVerdictPacket.start, first,
      Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
      Bool.false_eq_true, if_false, Option.bind_some]
    have tail := ih (base + 1) output.moveLeft next
    simpa only [NativeVerdictPacket.start, Nat.add_assoc, Nat.add_comm 1, Function.iterate_succ_apply] using tail

theorem rewind_checked (count : Nat) (input output : Tape) :
    NativeDeterministic.run (rewind count) (count + 1) (NativeVerdictPacket.start 0 input output) =
      some ({pc := count, inputTape := input, outputTape := (Tape.moveLeft^[count]) output, halted := true} : Machine.Configuration) := by
  rw [NativeDeterministic.run_add]
  have located : ∀ index, index < count → (rewind count)[0 + index]? = some (.native (.moveLeft .output)) := by
    intro index inside
    simp only [rewind, Nat.zero_add]
    rw [List.getElem?_append_left (by simpa only [List.length_replicate] using inside)]
    simp [inside]
  rw [moves_run _ 0 count input output located, Option.bind_some]
  have halt : (rewind count)[count]? = some (.native .halt) := by simp [rewind]
  simp [NativeDeterministic.run, NativeDeterministic.next?, NativeVerdictPacket.start, halt, Machine.Instruction.next]

theorem rewind_timed {State : Type} (count : Nat) (oracle : BitOracle State) (input output : Tape)
    (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (rewind count) oracle) (count + 1)
      (⟨state, .running (NativeVerdictPacket.start 0 input output), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running {pc := count, inputTape := input, outputTape := (Tape.moveLeft^[count]) output, halted := true}, trace⟩ :=
  NativeDeterministic.run_sound _ _ _ _ _ _ _ (rewind_checked count input output)

theorem timed {State : Type} (mask : List Bool) (oracle : BitOracle State) (input output : Tape)
    (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (code mask) oracle) (3 * mask.length + 4)
      (⟨state, .running (NativeVerdictPacket.start 0 input output), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish mask input output), trace⟩ := by
  have prefixRun := NativeDeterministic.run_return (NativeVerdictPacket.code mask) (rewind mask.length)
    (2 * mask.length + 3) (NativeVerdictPacket.start 0 input output) (NativeVerdictPacket.finish mask input output)
    rfl rfl (NativeVerdictPacket.checked mask input output)
  have prefixLaw := NativeDeterministic.run_sound _ oracle state trace _ _ _ prefixRun
  rw [show 3 * mask.length + 4 = (2 * mask.length + 3) + (mask.length + 1) by omega, TimedExecution.eval_add]
  change ((TimedExecution.eval (Reification.timedStep (HaltReturn.host (NativeVerdictPacket.code mask) (rewind mask.length)) oracle)
    (2 * mask.length + 3) _).bind _) = _
  rw [prefixLaw, PMF.pure_bind]
  change TimedExecution.eval (Reification.timedStep (HaltReturn.host (NativeVerdictPacket.code mask) (rewind mask.length)) oracle)
    (mask.length + 1) (CodeRelocation.frame (NativeVerdictPacket.code mask).length
      ⟨state, .running (NativeVerdictPacket.start 0 input (NativeVerdictPacket.finish mask input output).outputTape), trace⟩) = _
  rw [HaltReturn.body_eval, rewind_timed, PMF.pure_map]
  simp only [finish, restored, NativeVerdictPacket.finish, NativeVerdictPacket.result_length,
    CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

/-- The exact overwritten region is visible in the postcondition. -/
theorem restored_layout (output : Tape) (bits : List Bool) :
    restored output bits = {left := output.left, current := output.current, right := bits.map some ++ output.right.drop bits.length} := by
  induction bits generalizing output with
  | nil => cases output; rfl
  | cons bit rest ih =>
    simp only [restored, NativeVerdictPacket.written, List.length_cons, Function.iterate_succ_apply']
    change Tape.moveLeft (restored (output.moveRight.write (some bit)) rest) = _
    rw [ih]
    cases output with
    | mk left current right => cases right <;> simp [Tape.moveRight, Tape.write, Tape.moveLeft]


def read (count : Nat) (output : Tape) : List Bool := (output.right.take count).map (fun cell => cell.getD false)

theorem read_restored (output : Tape) (bits : List Bool) : read bits.length (restored output bits) = bits := by
  rw [read, restored_layout]
  simp

end CryptoOracle.Interactive.NativeVerdictRestore
