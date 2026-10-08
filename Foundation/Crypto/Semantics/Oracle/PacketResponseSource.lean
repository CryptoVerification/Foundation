import Foundation.Crypto.Semantics.Machine.NativePacketService
import Foundation.Crypto.Semantics.Oracle.NativeCallback

/-! Reusable callers of components that already return actual raw packets.
The component performs its own request loading and export. This controller
transfers that packet, writes it into the caller, then releases the caller.
No response is computed from a logical encoder at runtime. -/
namespace CryptoOracle.Interactive.PacketResponseSource
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

inductive Control (Component : Type u) (State : Type v) (Saved : Type w) where
  | source (retained : Saved) (frame : Configuration State)
  | processing (caller : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool) (component : Component)
  | returning (retained : Saved) (caller : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (loader : Machine.NativePacketService.Control)

variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool))
    (code : Code) (oracle : BitOracle State)

noncomputable def step : Control Component State Saved → PMF (Control Component State Saved)
  | .source retained frame =>
      match frame.control with
      | .awaiting caller request =>
          PMF.pure (.processing caller frame.state frame.reverseTrace request (begin retained request))
      | _ => (Reification.timedStep code oracle frame).map (.source retained)
  | .processing caller state trace request component =>
      match ready component with
      | some (retained, packet) =>
          PMF.pure (.returning retained caller state ((request, packet) :: trace) (.loading packet {}))
      | none => (componentStep component).map (.processing caller state trace request)
  | .returning retained caller state trace (.prepared loaded) =>
      PMF.pure (.source retained ⟨state, .running {caller with outputTape := loaded.outputTape}, trace⟩)
  | .returning retained caller state trace loader =>
      (Machine.NativePacketService.step [] loader).map (.returning retained caller state trace)

theorem writing (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining before : List Bool) :
    TimedExecution.eval (step componentStep begin ready code oracle) (2 * remaining.length + 1)
      (.returning retained caller state trace (.loading remaining {left := before.reverse.map some})) =
      PMF.pure (.returning retained caller state trace (.rewinding {left := (before ++ remaining).reverse.map some})) := by
  induction remaining generalizing before with
  | nil => simp [TimedExecution.eval, step, Machine.NativePacketService.step, PMF.pure_map]
  | cons bit rest ih =>
      rw [show 2 * (bit :: rest).length + 1 = ((2 * rest.length + 1) + 1) + 1 by simp; omega, TimedExecution.eval]
      simp only [step, Machine.NativePacketService.step, PMF.pure_map, PMF.pure_bind]
      rw [TimedExecution.eval]
      simp only [step, Machine.NativePacketService.step, PMF.pure_map, PMF.pure_bind]
      simpa [Machine.Tape.write, Machine.Tape.moveRight, List.reverse_append, List.map_append,
        List.append_assoc] using ih (before ++ [bit])

theorem rewind (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (left : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    TimedExecution.eval (step componentStep begin ready code oracle) (left.length + 2)
      (.returning retained caller state trace (.rewinding ⟨left.map some, current, right⟩)) =
      PMF.pure (.source retained ⟨state, .running {caller with outputTape := ResponseLoading.fromCells (left.reverse.map some ++ current :: right)}, trace⟩) := by
  induction left generalizing current right with
  | nil => simp [TimedExecution.eval, step, Machine.NativePacketService.step, ResponseLoading.fromCells, PMF.pure_map, PMF.pure_bind]
  | cons bit left ih =>
      rw [show (bit :: left).length + 2 = (left.length + 2) + 1 by rfl, TimedExecution.eval]
      simp only [step, Machine.NativePacketService.step, List.map_cons, Machine.Tape.moveLeft,
        PMF.pure_map, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem load_run (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (packet : List Bool) :
    TimedExecution.eval (step componentStep begin ready code oracle) (3 * packet.length + 3)
      (.returning retained caller state trace (.loading packet {})) =
      PMF.pure (.source retained ⟨state, .running {caller with outputTape := ResponseLoading.loaded packet}, trace⟩) := by
  rw [show 3 * packet.length + 3 = (2 * packet.length + 1) + (packet.length + 2) by omega, eval_add]
  have hw := writing componentStep begin ready code oracle retained caller state trace packet []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at hw
  rw [hw, PMF.pure_bind]
  have hr := rewind componentStep begin ready code oracle retained caller state trace packet.reverse none []
  simpa only [List.length_reverse, List.reverse_reverse, ResponseLoading.loaded] using hr

include componentStep begin ready code oracle in
theorem return_run (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (component : Component) (retained : Saved) (packet : List Bool)
    (hReady : ready component = some (retained, packet)) :
    TimedExecution.eval (step componentStep begin ready code oracle) (3 * packet.length + 4)
      (.processing caller state trace request component) =
      PMF.pure (.source retained (NativeCallback.resumed caller state trace request packet)) := by
  rw [show 3 * packet.length + 4 = (3 * packet.length + 3) + 1 by omega, TimedExecution.eval]
  simp only [step, hReady, PMF.pure_bind]
  exact load_run componentStep begin ready code oracle retained caller state ((request, packet) :: trace) packet

end CryptoOracle.Interactive.PacketResponseSource
