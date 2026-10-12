import Foundation.Crypto.Semantics.Oracle.BackwardFieldCopy
import Foundation.Crypto.Semantics.Oracle.NativeCode

/-! A four-instruction left scan to a represented blank boundary, followed by
one real right movement. The tape and its saved context are never written. -/
namespace CryptoOracle.Interactive.LeftBlankRewind
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def body (id : TapeId) : Code :=
  [.native (.branch id 3 1 1), .native (.moveLeft id), .native (.jump 0), .native (.moveRight id)]

def code (id : TapeId) (tail : Code) : Code := CodeRelocation.host (body id) tail

theorem body_length (id : TapeId) : (body id).length = 4 := rfl

theorem body_native (id : TapeId) : ∀ op ∈ body id, ∃ native, op = .native native := by
  intro op hm
  simp only [body, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

def put (id : TapeId) (tape other : Tape) : Machine.Configuration :=
  match id with
  | .input => { inputTape := tape, outputTape := other }
  | .output => { inputTape := other, outputTape := tape }

theorem cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (id : TapeId) (tail : Code)
    (bit : Bool) (right cells : List (Option Bool)) (other : Tape) :
    TimedExecution.eval (Reification.timedStep (code id tail) oracle) 3
      (NativeCode.frame state trace (put id (FixedWidthCopy.backwardFrontier right (some bit :: cells)) other)) =
      PMF.pure (NativeCode.frame state trace (put id (FixedWidthCopy.backwardFrontier (some bit :: right) cells) other)) := by
  cases id <;> cases bit <;> cases cells <;>
    simp [code, body, put, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
      Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
      transition, Machine.Instruction.next, Machine.Configuration.advance,
      Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
      Tape.moveLeft]

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (id : TapeId) (tail : Code)
    (bits : List Bool) (right left : List (Option Bool)) (other : Tape) :
    TimedExecution.eval (Reification.timedStep (code id tail) oracle) (3 * bits.length + 2)
      (NativeCode.frame state trace (put id (FixedWidthCopy.backwardFrontier right (bits.map some ++ none :: left)) other)) =
      PMF.pure (CodeRelocation.frame 4
        (NativeCode.frame state trace (put id (FixedWidthCopy.frontier (none :: left) (bits.reverse.map some ++ right)) other))) := by
  induction bits generalizing right with
  | nil =>
      cases id <;> cases right <;>
        simp [code, body, put, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
          Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
          transition, Machine.Instruction.next, Machine.Configuration.advance,
          Machine.Configuration.updateTape, Machine.Configuration.tape, FixedWidthCopy.backwardFrontier,
          FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight,
          CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 2 = 3 + (3 * rest.length + 2) from by simp; omega,
        TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append]
      rw [cell_run, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

end CryptoOracle.Interactive.LeftBlankRewind
