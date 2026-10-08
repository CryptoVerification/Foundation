import Foundation.Crypto.Semantics.Oracle.ReificationExecution

/-! The existing controller exports a contiguous request from a physical
tape, reversing the collected buffer one cell at a time. It retains the saved
source configuration, opaque oracle state and transcript. -/
namespace CryptoOracle.Interactive.RequestExport
open Foundation.Probability Machine
universe u
set_option backward.isDefEq.respectTransparency false

def packetTape (before after : List (Option Bool)) (bits : List Bool) : Tape :=
  { left := before, current := (bits.map some ++ none :: after).headD none,
    right := (bits.map some ++ none :: after).tail }

variable {State : Type u} (code : Code) (oracle : BitOracle State)

theorem collect (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (bits reversed : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (bits.length + 1)
      (⟨state, .sending machine (packetTape before after bits) reversed, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .reversing machine (bits.reverse ++ reversed) [], trace⟩ := by
  induction bits generalizing reversed before with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, packetTape]
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, packetTape, List.map_cons,
        List.cons_append, List.headD_cons, List.tail_cons, Tape.moveRight, PMF.pure_bind]
      cases bits <;>
        simpa [packetTape, List.reverse_cons, List.append_assoc] using ih (bit :: reversed) (some bit :: before)

theorem reverse (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) (remaining.length + 1)
      (⟨state, .reversing machine remaining request, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩ := by
  induction remaining generalizing request with
  | nil =>
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 2)
      (⟨state, .sending machine (packetTape before after request) [], trace⟩ : Configuration State) =
    PMF.pure ⟨state, .awaiting machine request, trace⟩ := by
  rw [show 2 * request.length + 2 = (request.length + 1) + (request.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse]
  simp

end CryptoOracle.Interactive.RequestExport
