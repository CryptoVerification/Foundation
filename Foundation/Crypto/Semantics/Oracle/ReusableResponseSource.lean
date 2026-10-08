import Foundation.Crypto.Semantics.Oracle.NativeCallback

/-! Reusable private response controller. A real source request starts a
component with the retained private store. Native export and response loading
return the existing store to the source before its next instruction executes.
Concrete `begin` and `ready` views must only transfer existing runtime data. -/
namespace CryptoOracle.Interactive.ReusableResponseSource
open Foundation.Probability TimedExecution
universe u v w

inductive Control (Component : Type u) (State : Type v) (Saved : Type w) where
  | source (retained : Saved) (frame : Configuration State)
  | processing (caller : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool) (component : Component)
  | calling (caller : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool)
      (callback : NativeCallback.Control State) (retained : Saved)

variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)

noncomputable def step : Control Component State Saved → PMF (Control Component State Saved)
  | .source retained frame =>
      match frame.control with
      | .awaiting caller request =>
          PMF.pure (.processing caller frame.state frame.reverseTrace request (begin retained request))
      | _ => (Reification.timedStep code oracle frame).map (.source retained)
  | .processing caller state trace request component =>
      match ready component with
      | some frame => PMF.pure (.calling caller state trace request (.responding (.running frame.1)) frame.2)
      | none => (componentStep component).map (.processing caller state trace request)
  | .calling _ _ _ _ (.source ⟨state, .running machine, trace⟩) retained =>
      PMF.pure (.source retained ⟨state, .running machine, trace⟩)
  | .calling caller state trace request callback retained =>
      (NativeCallback.step native code oracle caller state trace request callback).map
        (fun next => .calling caller state trace request next retained)

/-- Actual request data and the private store are passed unchanged. -/
theorem request_step (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :
    step componentStep begin ready native code oracle
      (.source retained ⟨state, .awaiting caller request, trace⟩) =
      PMF.pure (.processing caller state trace request (begin retained request)) := rfl

/-- The release transition precedes the caller's next instruction. -/
theorem resume_step (retained : Saved) (caller machine : Machine.Configuration) (state nextState : State)
    (trace nextTrace : List (List Bool × List Bool)) (request : List Bool) :
    step componentStep begin ready native code oracle
      (.calling caller state trace request (.source ⟨nextState, .running machine, nextTrace⟩) retained) =
      PMF.pure (.source retained ⟨nextState, .running machine, nextTrace⟩) := rfl

end CryptoOracle.Interactive.ReusableResponseSource
