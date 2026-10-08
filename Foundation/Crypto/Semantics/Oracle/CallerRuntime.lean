import Foundation.Crypto.Semantics.Oracle.SourcePrefix

/-! The minimal physical interface for a caller runtime. Native execution
before a request simulates the existing source machine; request transfer is
one actual transition; genuine terminal frames are absorbing. There is no
assumption about how private components prepare or deliver their replies. -/
namespace CryptoOracle.Interactive.CallerRuntime
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

structure Runtime {State : Type u} (Saved : Type v) (Target : Type w)
    (code : Code) (oracle : BitOracle State) where
  step : Target → PMF Target
  embed : Saved → Configuration State → Target
  boundary : Target → Bool
  embed_boundary : ∀ retained frame, boundary (embed retained frame) = SourcePrefix.boundary frame
  source_step : ∀ retained frame, SourcePrefix.boundary frame = false →
    step (embed retained frame) = (Reification.timedStep code oracle frame).map (embed retained)
  request : Saved → Machine.Configuration → State → List (List Bool × List Bool) → List Bool → Target
  request_step : ∀ retained caller state trace requestBits,
    step (embed retained ⟨state, .awaiting caller requestBits, trace⟩) =
      PMF.pure (request retained caller state trace requestBits)
  terminal : ∀ retained frame, Reification.terminal frame.control = true →
    step (embed retained frame) = PMF.pure (embed retained frame)

namespace Runtime

variable {State : Type u} {Saved : Type v} {Target : Type w}
    {code : Code} {oracle : BitOracle State} (R : Runtime Saved Target code oracle)

abbrev Source := Saved × Configuration State

def source (value : Source (State := State) (Saved := Saved)) : Target := R.embed value.1 value.2

noncomputable def selection (retained : Saved) :=
  (SourcePrefix.localProcedure code oracle).liftBoundary SourcePrefix.boundary
    (fun input _ h => input.complete _ h)
    (fun frame h => by simp [SourcePrefix.step, h])
    (fun _ frame => frame) (fun _ _ => rfl)
    R.step R.boundary (R.embed retained) (R.embed_boundary retained)
    (fun frame h => by rw [SourcePrefix.step, h]; exact R.source_step retained frame h)

theorem prefix_entry (retained : Saved) (input : SourcePrefix.Input code oracle) :
    (R.selection retained).entry input = R.embed retained input.start := rfl

theorem prefix_budget (retained : Saved) (input : SourcePrefix.Input code oracle) :
    (R.selection retained).budget input = input.budget := rfl

theorem prefix_semantics (retained : Saved) (input : SourcePrefix.Input code oracle) :
    (R.selection retained).semantics input =
      TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start := rfl

/-- Private values and delivery implementations do not affect how the
actual public caller reaches its next request or termination. -/
theorem prefix_private_independence (first second : Saved) (input : SourcePrefix.Input code oracle) :
    (R.selection first).costed input = (R.selection second).costed input := rfl

noncomputable def transfer (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Procedure R.step Unit Unit :=
  Procedure.ofFixed R.step (fun _ => R.embed retained ⟨state, .awaiting caller request, trace⟩)
    (fun _ _ => R.request retained caller state trace request) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, R.request_step, PMF.pure_map])

end Runtime
end CryptoOracle.Interactive.CallerRuntime
