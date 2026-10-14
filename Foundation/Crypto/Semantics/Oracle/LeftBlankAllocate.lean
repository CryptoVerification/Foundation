import Foundation.Crypto.Semantics.Oracle.LeftBlankRewind

/-! Cross the first represented blank on the left by one actual left move.
This allocates a fresh key-save cell outside the retained fuel boundary. -/
namespace CryptoOracle.Interactive.LeftBlankAllocate
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
def body : Code :=
  [.native (.branch .input 3 1 1), .native (.moveLeft .input), .native (.jump 0), .native (.moveLeft .input)]
def code (tail : Code) : Code := CodeRelocation.host body tail

theorem cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (bit : Bool)
    (right cells : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) 3
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.backwardFrontier right (some bit :: cells), outputTape := output }) =
      PMF.pure (NativeCode.frame state trace { inputTape := FixedWidthCopy.backwardFrontier (some bit :: right) cells, outputTape := output }) := by
  cases bit <;> cases cells <;>
    simp [code, body, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
      Tape.moveLeft]

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (bits : List Bool)
    (right : List (Option Bool)) (output : Tape) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) (3 * bits.length + 2)
      (NativeCode.frame state trace { inputTape := FixedWidthCopy.backwardFrontier right (bits.map some ++ [none]), outputTape := output }) =
      PMF.pure (CodeRelocation.frame 4
        (NativeCode.frame state trace { inputTape := { right := none :: bits.reverse.map some ++ right }, outputTape := output })) := by
  induction bits generalizing right with
  | nil =>
      simp [code, body, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
        transition, Machine.Instruction.next, Machine.Configuration.advance,
        Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
        Tape.moveLeft, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 2 = 3 + (3 * rest.length + 2) from by simp; omega,
        TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append]
      rw [cell_run, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem body_native : ∀ op ∈ body, ∃ native, op = .native native := by
  intro op hm
  simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
end CryptoOracle.Interactive.LeftBlankAllocate
