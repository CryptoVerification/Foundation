import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource

/-! Physical response loading and release to a reusable source. The retained
store and suspended caller remain actual runtime values, with no tape reset. -/
namespace CryptoOracle.Interactive.ReusableResponseReturn
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

def embedLoader (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (retained : Saved) (frame : Configuration State) : ReusableResponseSource.Control Component State Saved :=
  .calling saved state trace request (.source frame) retained

theorem writing_run (published : List (List Bool × List Bool)) (retained : Saved) (remaining before : List Bool) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (2 * remaining.length + 1)
      (embedLoader saved state trace request retained ⟨state, .loading saved remaining
        { left := before.reverse.map some }, published⟩) =
      PMF.pure (embedLoader saved state trace request retained
        ⟨state, .rewinding saved { left := (before ++ remaining).reverse.map some }, published⟩) := by
  induction remaining generalizing before with
  | nil =>
      simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, embedLoader, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show 2 * (bit :: remaining).length + 1 = ((2 * remaining.length + 1) + 1) + 1 by simp; omega,
        TimedExecution.eval]
      simp only [outerStep, ReusableResponseSource.step, embedLoader, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      rw [TimedExecution.eval]
      simp only [outerStep, ReusableResponseSource.step, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [embedLoader, Machine.Tape.write, Machine.Tape.moveRight, List.reverse_append,
        List.map_append, List.append_assoc] using ih (before ++ [bit])

theorem rewind_run (published : List (List Bool × List Bool)) (retained : Saved) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (left.length + 1)
      (embedLoader saved state trace request retained
        ⟨state, .rewinding saved ⟨left.map some, current, right⟩, published⟩) =
      PMF.pure (embedLoader saved state trace request retained
        ⟨state, .running { saved with outputTape := ResponseLoading.fromCells (left.reverse.map some ++ current :: right) }, published⟩) := by
  induction left generalizing current right with
  | nil =>
      simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, embedLoader, NativeCallback.step,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
        transition, ResponseLoading.fromCells, PMF.pure_map]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [outerStep, ReusableResponseSource.step, embedLoader, NativeCallback.step, Reification.timedStep,
        Reification.terminal, Bool.false_eq_true, ↓reduceIte, Reification.perform,
        Reification.action, transition, List.map_cons, Machine.Tape.moveLeft, PMF.pure_map, PMF.pure_bind]
      simp only [embedLoader] at ih
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]


theorem loading_run (published : List (List Bool × List Bool)) (retained : Saved) (packet : List Bool) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (3 * packet.length + 2)
      (embedLoader saved state trace request retained ⟨state, .loading saved packet {}, published⟩) =
      PMF.pure (embedLoader saved state trace request retained
        ⟨state, .running { saved with outputTape := ResponseLoading.loaded packet }, published⟩) := by
  rw [show 3 * packet.length + 2 = (2 * packet.length + 1) + (packet.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add]
  have h := writing_run componentStep begin ready native code oracle saved state trace request published retained packet []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at h
  rw [h, PMF.pure_bind, rewind_run]
  simp [embedLoader, ResponseLoading.loaded]

/-- Export has already returned the physical packet. Loading and release
charge every response bit and one additional caller ownership transfer. -/
theorem packet_return (retained : Saved) (packet : List Bool) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) (3 * packet.length + 4)
      (.calling saved state trace request (.responding (.returned packet)) retained) =
      PMF.pure (.source retained (NativeCallback.resumed saved state trace request packet)) := by
  rw [show 3 * packet.length + 4 = ((3 * packet.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [outerStep, ReusableResponseSource.step, NativeCallback.step, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (outerStep componentStep begin ready native code oracle) (3 * packet.length + 2) 1]
  have h := loading_run componentStep begin ready native code oracle saved state trace request
    ((request, packet) :: trace) retained packet
  change (TimedExecution.eval (outerStep componentStep begin ready native code oracle) (3 * packet.length + 2)
    (embedLoader saved state trace request retained
      ⟨state, .loading saved packet {}, (request, packet) :: trace⟩)).bind
    (TimedExecution.eval (outerStep componentStep begin ready native code oracle) 1) = _
  rw [h, PMF.pure_bind]
  simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, embedLoader, NativeCallback.resumed]

noncomputable def procedure (retained : Saved) :
    Procedure (outerStep componentStep begin ready native code oracle) (List Bool) Unit :=
  Procedure.ofFixed _
    (fun packet => .calling saved state trace request (.responding (.returned packet)) retained)
    (fun packet _ => .source retained (NativeCallback.resumed saved state trace request packet))
    (fun _ => PMF.pure ()) (fun packet => 3 * packet.length + 4)
    (fun packet => by simpa only [PMF.pure_map] using
      (packet_return componentStep begin ready native code oracle saved state trace request retained packet))

end CryptoOracle.Interactive.ReusableResponseReturn
