import Foundation.Crypto.Semantics.Oracle.UnaryFuel
import Foundation.Crypto.Semantics.Oracle.RightBlankSeek

/-! Move a unary true field from output to fresh input cells left of a retained
table. Source counter cells are explicitly cleared; the saved query is retained. -/
namespace CryptoOracle.Interactive.UnaryCounterTransfer
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def body : Code :=
  [.native (.branch .output 6 6 1), .native (.write .input true),
   .native (.erase .output), .native (.moveLeft .input),
   .native (.moveRight .output), .native (.jump 0)]
def code (tail : Code) : Code := CodeRelocation.host body tail

theorem cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (inputRight outputLeft outputRight : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) 6
      (NativeCode.frame state trace { inputTape := { right := inputRight }, outputTape := FixedWidthCopy.frontier outputLeft (some true :: outputRight) }) =
      PMF.pure (NativeCode.frame state trace { inputTape := { right := some true :: inputRight }, outputTape := FixedWidthCopy.frontier (none :: outputLeft) outputRight }) := by
  cases outputRight <;>
    simp [code, body, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells, Tape.moveRight, Tape.moveLeft, Tape.write]

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (inputRight outputLeft query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) (6 * fuel + 1)
      (NativeCode.frame state trace { inputTape := { right := inputRight }, outputTape := FixedWidthCopy.frontier outputLeft (List.replicate fuel (some true) ++ none :: query) }) =
      PMF.pure (CodeRelocation.frame 6
        (NativeCode.frame state trace { inputTape := { right := List.replicate fuel (some true) ++ inputRight }, outputTape := { left := List.replicate fuel none ++ outputLeft, right := query } })) := by
  induction fuel generalizing inputRight outputLeft with
  | zero =>
      simp [code, body, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
        transition, Machine.Instruction.next, Machine.Configuration.tape, FixedWidthCopy.frontier,
        ResponseLoading.fromCells, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  | succ fuel ih =>
      rw [show 6 * (fuel + 1) + 1 = 6 + (6 * fuel + 1) from by omega, TimedExecution.eval_add]
      simp only [List.replicate_succ, List.cons_append]
      rw [cell_run, PMF.pure_bind, ih, UnaryFuel.replicate_push, UnaryFuel.replicate_push]
      rfl

theorem body_native : ∀ op ∈ body, ∃ native, op = .native native := by
  intro op hm
  simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

end CryptoOracle.Interactive.UnaryCounterTransfer
