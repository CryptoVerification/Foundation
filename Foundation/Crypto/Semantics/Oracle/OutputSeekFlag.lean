import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy
import Foundation.Crypto.Semantics.Oracle.CodeRelocation

/-! Recover the response flag after a terminal comparison failed at any cell.
Scan right to the explicit blank and move left once. No cell is erased and the
private input tape is retained. The scan is one fixed four-instruction loop. -/
namespace CryptoOracle.Interactive.OutputSeekFlag
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def scanPrefix : Code :=
  [.native (.branch .output 3 1 1), .native (.moveRight .output),
   .native (.jump 0), .native (.moveLeft .output)]

def code (tail : Code) : Code := CodeRelocation.host scanPrefix tail

theorem code_length (tail : Code) : (code tail).length = 4 + tail.length := by
  rw [code, CodeRelocation.code_length]
  rfl

theorem code_native (tail : Code) (ht : ∀ i ∈ tail, ∃ op, i = .native op) :
    ∀ i ∈ code tail, ∃ op, i = .native op := by
  apply CodeRelocation.host_native _ _ _ ht
  intro i hi
  simp only [scanPrefix, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem iteration (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Tape) (tail : Code)
    (left cells : List (Option Bool)) (bit : Bool) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) 3
      (⟨state, .running { pc := 0, inputTape := input, outputTape := FixedWidthCopy.frontier left (some bit :: cells) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 0, inputTape := input, outputTape := FixedWidthCopy.frontier (some bit :: left) cells }, trace⟩ := by
  cases bit <;> cases cells <;>
    simp [code, scanPrefix, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.moveRight]

/-- Charge every scanned cell and the final branch/move-left pair. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Tape) (tail : Code)
    (left : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) (3 * bits.length + 2)
      (⟨state, .running { pc := 0, inputTape := input, outputTape := FixedWidthCopy.frontier left (bits.map some ++ [none]) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 4, inputTape := input, outputTape := ({ left := bits.reverse.map some ++ left } : Tape).moveLeft }, trace⟩ := by
  induction bits generalizing left with
  | nil =>
      simp [code, scanPrefix, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
        Reification.terminal, Reification.perform, Reification.action, transition,
        Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
        Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells]
  | cons bit rest ih =>
      rw [show 3 * (bit :: rest).length + 2 = 3 + (3 * rest.length + 2) from by simp; omega,
        TimedExecution.eval_add]
      simp only [List.map_cons, List.cons_append]
      rw [iteration, PMF.pure_bind, ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- From any mismatch position, recover precisely the original flag entry.
The unvisited cells and saved left context may contain arbitrary data. -/
theorem recover (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Tape) (tail : Code)
    (past rest : List Bool) (current flag : Bool) (before' : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code tail) oracle) (3 * (past.length + 2) + 2)
      (⟨state, .running { pc := 0, inputTape := input, outputTape := FixedWidthCopy.backwardFrontier (past.reverse.map some ++ [some flag, none]) ((current :: rest).map some ++ before') }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := 4, inputTape := input, outputTape := { left := (past ++ current :: rest).map some ++ before', current := some flag, right := [none] } }, trace⟩ := by
  have hstart : FixedWidthCopy.backwardFrontier (past.reverse.map some ++ [some flag, none])
      ((current :: rest).map some ++ before') =
      FixedWidthCopy.frontier (rest.map some ++ before')
        ((current :: (past.reverse ++ [flag])).map some ++ [none]) := by
    simp [FixedWidthCopy.backwardFrontier, FixedWidthCopy.frontier, ResponseLoading.fromCells,
      List.map_append, List.append_assoc]
  have hrun := run oracle state trace input tail (rest.map some ++ before')
    (current :: (past.reverse ++ [flag]))
  rw [hstart]
  have hlen : (current :: (past.reverse ++ [flag])).length = past.length + 2 := by simp
  rw [hlen] at hrun
  rw [hrun]
  simp [List.reverse_append, List.reverse_cons, List.map_append, List.append_assoc, Tape.moveLeft]

end CryptoOracle.Interactive.OutputSeekFlag
