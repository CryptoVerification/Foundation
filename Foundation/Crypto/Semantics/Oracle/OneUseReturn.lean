import Foundation.Crypto.Semantics.Oracle.OneUseSource

/-! Actual response loading and return in the one-use outer controller.
The use flag and physical private store survive all charged transfers. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

def embedLoader (key second : Machine.Tape) (frame : Configuration State) : Control State :=
  .handling spent saved state trace request (.calling key second (.source frame))

theorem writing_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (remaining before : List Bool) :
    TimedExecution.eval (step native code oracle) (2 * remaining.length + 1)
      (embedLoader spent saved state trace request key second ⟨state, .loading saved remaining
        { left := before.reverse.map some }, published⟩) =
      PMF.pure (embedLoader spent saved state trace request key second
        ⟨state, .rewinding saved { left := (before ++ remaining).reverse.map some }, published⟩) := by
  induction remaining generalizing before with
  | nil =>
      simp [TimedExecution.eval, step, embedLoader, CheckedCallback.step, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega,
        TimedExecution.eval]
      simp only [step, embedLoader, CheckedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      rw [TimedExecution.eval]
      simp only [step, CheckedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [embedLoader, Machine.Tape.write, Machine.Tape.moveRight, List.reverse_append,
        List.map_append, List.append_assoc] using ih (before ++ [bit])

theorem rewind_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (left.length + 1)
      (embedLoader spent saved state trace request key second
        ⟨state, .rewinding saved ⟨left.map some, current, right⟩, published⟩) =
      PMF.pure (embedLoader spent saved state trace request key second
        ⟨state, .running { saved with outputTape := ResponseLoading.fromCells (left.reverse.map some ++ current :: right) }, published⟩) := by
  induction left generalizing current right with
  | nil =>
      simp [TimedExecution.eval, step, embedLoader, CheckedCallback.step, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
        transition, ResponseLoading.fromCells, PMF.pure_map]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, embedLoader, CheckedCallback.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, List.map_cons, Machine.Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
      simp only [embedLoader] at ih
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- The actual response loader reaches the outer controller's first resume
point. Its transcript is a runtime value, not rebuilt by a proof reader. -/
theorem loading_run (published : List (List Bool × List Bool)) (key second : Machine.Tape) (packet : List Bool) :
    TimedExecution.eval (step native code oracle) (3 * packet.length + 2)
      (embedLoader spent saved state trace request key second ⟨state, .loading saved packet {}, published⟩) =
      PMF.pure (embedLoader spent saved state trace request key second
        ⟨state, .running { saved with outputTape := ResponseLoading.loaded packet }, published⟩) := by
  rw [show 3 * packet.length + 2 = (2 * packet.length + 1) + (packet.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add]
  have h := writing_run native code oracle spent saved state trace request published key second packet []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at h
  rw [h, PMF.pure_bind, rewind_run]
  simp [embedLoader, ResponseLoading.loaded]

theorem packet_return (key second : Machine.Tape) (packet : List Bool) :
    TimedExecution.eval (step native code oracle) (3 * packet.length + 4)
      (.handling spent saved state trace request (.calling key second (.responding (.returned packet)))) =
      PMF.pure (.source spent key (NativeCallback.resumed saved state trace request packet)) := by
  rw [show 3 * packet.length + 4 = ((3 * packet.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [step, CheckedCallback.step, NativeCallback.step, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (step native code oracle) (3 * packet.length + 2) 1]
  have h := loading_run native code oracle spent saved state trace request ((request, packet) :: trace) key second packet
  change (TimedExecution.eval (step native code oracle) (3 * packet.length + 2)
    (embedLoader spent saved state trace request key second
      ⟨state, .loading saved packet {}, (request, packet) :: trace⟩)).bind
    (TimedExecution.eval (step native code oracle) 1) = _
  rw [h, PMF.pure_bind]
  simpa only [embedLoader, NativeCallback.resumed] using resume_transfer native code oracle spent saved
    { saved with outputTape := ResponseLoading.loaded packet } state state trace ((request, packet) :: trace) request key second

end CryptoOracle.Interactive.OneUseSource
