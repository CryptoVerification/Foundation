import Foundation.Crypto.Semantics.Oracle.ReificationExecution
import Foundation.Crypto.Semantics.Procedure

/-! The existing source controller loads arbitrary response bytes cell by
cell and resumes the saved native configuration. Its input tape, program
counter, oracle state and transcript are retained. The output tape is replaced
by the actual loaded response, including the represented final blank. -/
namespace CryptoOracle.Interactive.ResponseLoading
open Foundation.Probability TimedExecution Machine
universe u
set_option backward.isDefEq.respectTransparency false

def fromCells (cells : List (Option Bool)) : Tape := ⟨[], cells.headD none, cells.tail⟩

def loaded (response : List Bool) : Tape := fromCells (response.map some ++ [none])

variable {State : Type u} (code : Code) (oracle : BitOracle State)

theorem writing_run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining before : List Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * remaining.length + 1)
      (⟨state, .loading machine remaining { left := before.reverse.map some }, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .rewinding machine { left := (before ++ remaining).reverse.map some }, trace⟩ := by
  induction remaining generalizing before with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega]
      rw [TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, Reification.perform, Reification.action, transition, PMF.pure_bind]
      rw [TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, Reification.perform, Reification.action, transition, PMF.pure_bind]
      simpa [Tape.write, Tape.moveRight, List.reverse_append, List.map_append,
        List.append_assoc] using ih (before ++ [bit])

theorem rewinding_run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (left.length + 1)
      (⟨state, .rewinding machine ⟨left.map some, current, right⟩, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { machine with outputTape := fromCells (left.reverse.map some ++ current :: right) }, trace⟩ := by
  induction left generalizing current right with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, fromCells]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true,
        ↓reduceIte, Reification.perform, Reification.action, transition, List.map_cons,
        Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (response : List Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) (3 * response.length + 2)
      (⟨state, .loading machine response {}, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running { machine with outputTape := loaded response }, trace⟩ := by
  rw [show 3 * response.length + 2 = (2 * response.length + 1) + (response.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add]
  have h := writing_run code oracle machine state trace response []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at h
  rw [h, PMF.pure_bind, rewinding_run]
  simp [loaded]

theorem continues (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (response : List Bool) (horizon : Nat)
    (hBudget : 3 * response.length + 2 ≤ horizon) :
    TimedExecution.eval (Reification.timedStep code oracle) horizon
      (⟨state, .loading machine response {}, trace⟩ : Configuration State) =
    TimedExecution.eval (Reification.timedStep code oracle) (horizon - (3 * response.length + 2))
      ⟨state, .running { machine with outputTape := loaded response }, trace⟩ := by
  conv_lhs => rw [show horizon = (3 * response.length + 2) + (horizon - (3 * response.length + 2)) by omega,
    TimedExecution.eval_add, run, PMF.pure_bind]

structure Input (State : Type u) where
  machine : Machine.Configuration
  state : State
  trace : List (List Bool × List Bool)
  response : List Bool

/-- This is a contract for the source machine's actual response loader.
The resumed source can continue immediately; its exit need not absorb. -/
noncomputable def procedure : Procedure (Reification.timedStep code oracle) (Input State) Unit :=
  Procedure.ofFixed (Reification.timedStep code oracle)
    (fun input => ⟨input.state, .loading input.machine input.response {}, input.trace⟩)
    (fun input _ => ⟨input.state, .running { input.machine with outputTape := loaded input.response }, input.trace⟩)
    (fun _ => PMF.pure ()) (fun input => 3 * input.response.length + 2)
    (fun input => by simpa only [PMF.pure_map] using run code oracle input.machine input.state input.trace input.response)

end CryptoOracle.Interactive.ResponseLoading
