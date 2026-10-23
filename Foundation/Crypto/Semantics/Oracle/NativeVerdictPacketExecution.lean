import Foundation.Crypto.Semantics.Oracle.NativeVerdictPacket

namespace CryptoOracle.Interactive.NativeVerdictPacket
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

private theorem boundary_get (before : Code) (instruction : Interactive.Instruction) (after : Code) :
    (before ++ instruction :: after)[before.length]? = some instruction := by simp

theorem zero_located (mask : List Bool) : Located (code mask) 1 (mask.map fun _ => false) := by
  have site := located_append [Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))]
    (mask.map fun _ => false) ([Interactive.Instruction.native (.jump (4 * mask.length + 3))] ++ emit mask ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3)), Interactive.Instruction.native .halt])
  simpa only [code, List.append_assoc, List.length_singleton] using site

theorem one_located (mask : List Bool) : Located (code mask) (2 * mask.length + 2) mask := by
  have site := located_append
    ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3))]) mask [Interactive.Instruction.native (.jump (4 * mask.length + 3)), Interactive.Instruction.native .halt]
  have address : ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++ [Interactive.Instruction.native (.jump (4 * mask.length + 3))]).length = 2 * mask.length + 2 := by
    simp [emit_length]
  rw [address] at site
  simpa only [code, List.append_assoc] using site

theorem zero_jump (mask : List Bool) :
    (code mask)[2 * mask.length + 1]? = some (Interactive.Instruction.native (.jump (4 * mask.length + 3))) := by
  have site := boundary_get
    ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false))
    (Interactive.Instruction.native (.jump (4 * mask.length + 3))) (emit mask ++ [Interactive.Instruction.native (.jump (4 * mask.length + 3)), Interactive.Instruction.native .halt])
  simpa [code, emit_length, List.append_assoc, Nat.add_comm, Nat.add_assoc] using site

theorem one_jump (mask : List Bool) :
    (code mask)[4 * mask.length + 2]? = some (Interactive.Instruction.native (.jump (4 * mask.length + 3))) := by
  have site := boundary_get
    ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3))] ++ emit mask)
    (Interactive.Instruction.native (.jump (4 * mask.length + 3))) [Interactive.Instruction.native .halt]
  have address : ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3))] ++ emit mask).length = 4 * mask.length + 2 := by
    simp [emit_length]; omega
  rw [address] at site
  simpa only [code, List.append_assoc] using site

theorem halt_get (mask : List Bool) : (code mask)[4 * mask.length + 3]? = some (Interactive.Instruction.native .halt) := by
  have site := boundary_get
    ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3))] ++ emit mask ++ [Interactive.Instruction.native (.jump (4 * mask.length + 3))])
    (Interactive.Instruction.native .halt) []
  have address : ([Interactive.Instruction.native (.branch .output 1 1 (2 * mask.length + 2))] ++ emit (mask.map fun _ => false) ++
      [Interactive.Instruction.native (.jump (4 * mask.length + 3))] ++ emit mask ++ [Interactive.Instruction.native (.jump (4 * mask.length + 3))]).length =
        4 * mask.length + 3 := by simp [emit_length]; omega
  rw [address] at site
  simpa [code, List.append_assoc] using site

private theorem jump_halt (program : Code) (base target : Nat) (input output : Tape)
    (jump : program[base]? = some (Interactive.Instruction.native (.jump target))) (halt : program[target]? = some (Interactive.Instruction.native .halt)) :
    NativeDeterministic.run program 2 (start base input output) =
      some ({pc := target, inputTape := input, outputTape := output, halted := true} : Machine.Configuration) := by
  simp [NativeDeterministic.run, NativeDeterministic.next?, start, jump, halt, Instruction.next]

private theorem zero_body (mask : List Bool) (input output : Tape) :
    NativeDeterministic.run (code mask) (2 * mask.length + 2) (start 1 input output) =
      some ({pc := 4 * mask.length + 3, inputTape := input, outputTape := written output (mask.map fun _ => false), halted := true} : Machine.Configuration) := by
  rw [NativeDeterministic.run_add]
  have run := emit_checked (code mask) 1 input output (mask.map fun _ => false) (zero_located mask)
  simp only [List.length_map] at run
  rw [run, Option.bind_some]
  simpa only [emitFinish, start, List.length_map, Nat.add_comm 1] using jump_halt (code mask) (2 * mask.length + 1)
    (4 * mask.length + 3) input (written output (mask.map fun _ => false)) (zero_jump mask) (halt_get mask)

private theorem one_body (mask : List Bool) (input output : Tape) :
    NativeDeterministic.run (code mask) (2 * mask.length + 2) (start (2 * mask.length + 2) input output) =
      some ({pc := 4 * mask.length + 3, inputTape := input, outputTape := written output mask, halted := true} : Machine.Configuration) := by
  rw [NativeDeterministic.run_add, emit_checked _ _ _ _ _ (one_located mask), Option.bind_some]
  have address : 2 * mask.length + 2 + 2 * mask.length = 4 * mask.length + 2 := by omega
  simp only [emitFinish, address]
  exact jump_halt (code mask) (4 * mask.length + 2) (4 * mask.length + 3) input (written output mask)
    (one_jump mask) (halt_get mask)

/-- Symbolic in the whole mask and in arbitrary inherited tape contents.
Blank and zero verdict cells follow the same false branch. -/
theorem checked (mask : List Bool) (input output : Tape) :
    NativeDeterministic.run (code mask) (2 * mask.length + 3) (start 0 input output) =
      some (finish mask input output) := by
  rw [show 2 * mask.length + 3 = 1 + (2 * mask.length + 2) by omega, NativeDeterministic.run_add]
  have first : NativeDeterministic.run (code mask) 1 (start 0 input output) =
      some (start (if output.current.getD false then 2 * mask.length + 2 else 1) input output) := by
    cases cell : output.current with
    | none => simp [NativeDeterministic.run, NativeDeterministic.next?, code, start, Instruction.next, Machine.Configuration.tape, cell]
    | some bit => cases bit <;> simp [NativeDeterministic.run, NativeDeterministic.next?, code, start, Instruction.next, Machine.Configuration.tape, cell]
  rw [first, Option.bind_some]
  cases bit : output.current.getD false with
  | false => simpa [finish, result, bit] using zero_body mask input output
  | true => simpa [finish, result, bit] using one_body mask input output

/-- Exact real transition count; neither a vector write nor a free reset is
an instruction. The inherited oracle state and transcript remain untouched. -/
theorem timed {State : Type} (mask : List Bool) (oracle : BitOracle State)
    (input output : Tape) (state : State) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep (code mask) oracle) (2 * mask.length + 3)
      (⟨state, .running (start 0 input output), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (finish mask input output), trace⟩ :=
  NativeDeterministic.run_sound _ _ _ _ _ _ _ (checked mask input output)

end CryptoOracle.Interactive.NativeVerdictPacket
