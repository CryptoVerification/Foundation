import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy
import Foundation.Crypto.Semantics.Oracle.NativeCode

/-! Position a copied cache response for export. The preceding presence flag
is physically erased; the query prefix, the input tape and all response bits
are retained. This routine works also for an empty response. -/
namespace CryptoOracle.Interactive.NativePacketFlagResponse
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def actions (width : Nat) : List StraightLine.Action :=
  List.replicate (width + 1) (.left .output) ++ [.write .output none, .right .output]

@[simp] theorem actions_length (width : Nat) : (actions width).length = width + 3 := by
  simp [actions]

theorem execute (machine : Machine.Configuration) (packet : List Bool)
    (before : List (Option Bool)) :
    StraightLine.execute (actions packet.length)
      { machine with outputTape := { left := packet.reverse.map some ++ some true :: before } } =
      { machine with pc := machine.pc + packet.length + 3, outputTape := FixedWidthCopy.frontier (none :: before) (packet.map some ++ [none]) } := by
  have moved := StraightLine.rewind_output (some true :: packet.map some) before [] none machine
  simp only [List.length_cons, List.length_map, List.reverse_cons,
    List.singleton_append, List.append_assoc] at moved
  simp only [List.map_reverse]
  unfold actions
  rw [StraightLine.execute_append, moved]
  simp [StraightLine.execute, StraightLine.apply, StraightLine.rewindOutputTape,
    Configuration.updateTape, Configuration.advance, FixedWidthCopy.frontier,
    ResponseLoading.fromCells, Tape.write, Tape.moveRight, Nat.add_assoc]

  cases packet <;> rfl

/-- The same physical response-positioning code works with any input tape.
The source frame, rather than a particular table-lookup endpoint, supplies it. -/
theorem stage_run {State : Type*} (tail : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration) (packet : List Bool) (before : List (Option Bool))
    (pc : machine.pc = 0) (active : machine.halted = false)
    (layout : machine.outputTape = { left := packet.reverse.map some ++ some true :: before })
    (halt : Bool) :
    TimedExecution.eval (Reification.timedStep
      (StraightLine.code (actions packet.length) ++ [.native .halt] ++ tail) oracle)
      (packet.length + 3 + halt.toNat) (NativeCode.frame state trace machine) =
      PMF.pure (NativeCode.frame state trace
        { machine with pc := packet.length + 3, outputTape := FixedWidthCopy.frontier (none :: before) (packet.map some ++ [none]), halted := halt }) := by
  have shape : machine = { machine with outputTape := { left := packet.reverse.map some ++ some true :: before } } := by
    rw [← layout]
  have moved := StraightLine.public_run oracle state trace [] ([.native .halt] ++ tail)
    (actions packet.length) machine pc active
  simp only [List.nil_append, actions_length] at moved
  have executed := execute machine packet before
  rw [← shape] at executed
  rw [executed] at moved
  simp only [pc, Nat.zero_add] at moved
  rw [TimedExecution.eval_add]
  simp only [List.append_assoc] at ⊢
  simp only [NativeCode.frame] at moved ⊢
  rw [moved, PMF.pure_bind]
  have fetched : (StraightLine.code (actions packet.length) ++ [.native .halt] ++ tail)[packet.length + 3]? =
      some (.native .halt) := by
    rw [List.append_assoc, List.getElem?_append_right (by simp [StraightLine.code]),
      show packet.length + 3 - (StraightLine.code (actions packet.length)).length = 0 by simp [StraightLine.code]]
    rfl
  simp only [List.append_assoc, List.singleton_append] at fetched
  cases halt <;> simp [TimedExecution.eval, Reification.timedStep,
    Reification.terminal, Reification.perform, Reification.action, transition, fetched, active,
    Machine.Instruction.next]

end CryptoOracle.Interactive.NativePacketFlagResponse
