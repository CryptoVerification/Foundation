import Foundation.Crypto.Semantics.Oracle.ReusableResponseService
import Foundation.Crypto.Semantics.Oracle.ReusableSourceExecution

/-! User-facing composition of arbitrary certified source prefixes with
request-indexed component handlers. Physical handoff proofs are supplied by
the common response adapter; callers provide only operational certificates
and reachable-request resource bounds. -/
namespace CryptoOracle.Interactive.ReusableCertifiedSource
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (handler : ∀ retained request, ReusableResponseService.Handler.{u,w,x} componentStep ready (begin retained request))

noncomputable def service (retained : Saved) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  ReusableResponseService.procedure componentStep begin ready hAbsorb native code oracle
    retained caller state trace request (handler retained request)

noncomputable def kernel (retained : Saved) (frame : Configuration State) :=
  match frame.control with
  | .awaiting caller request =>
      ((handler retained request).execution.semantics ()).map (fun output =>
        ((handler retained request).retained output,
          NativeCallback.resumed caller frame.state frame.reverseTrace request ((handler retained request).encode output)))
  | _ => PMF.pure (retained, frame)

variable (retained : Saved) (cap : SourcePrefix.Input code oracle → Nat)
    (hCap : ∀ input frame,
      frame ∈ (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).support →
      ∀ caller request, frame.control = .awaiting caller request →
        (handler retained request).execution.budget () + (6 * (handler retained request).responseCap + 9) ≤ cap input)

noncomputable def round :=
  ReusableSourceRound.round componentStep begin ready native code oracle
    (service componentStep begin ready hAbsorb native code oracle handler)
    (fun _ _ _ _ _ => ReusableResponseService.entry _ _ _ _ _ _ _ _ _ _ _ _ _)
    (fun _ _ _ _ _ _ => rfl) retained cap
    (fun input frame h caller request hc => by
      rw [service, ReusableResponseService.budget]
      exact hCap input frame h caller request hc)

theorem budget (input : SourcePrefix.Input code oracle) :
    (round componentStep begin ready hAbsorb native code oracle handler retained cap hCap).budget input =
      input.budget + (1 + cap input) := rfl

theorem semantics (input : SourcePrefix.Input code oracle) :
    (round componentStep begin ready hAbsorb native code oracle handler retained cap hCap).semantics input =
      (TimedExecution.eval (SourcePrefix.step code oracle) input.budget input.start).bind
        (kernel componentStep begin ready handler retained) := by
  rw [round, ReusableSourceRound.round_semantics]
  congr 1
  funext frame
  rw [ReusableSourceRound.response_semantics]
  rcases frame with ⟨state, control, trace⟩
  cases control <;> try rfl
  exact ReusableResponseService.semantics _ _ _ _ _ _ _ _ _ _ _ _ _

end CryptoOracle.Interactive.ReusableCertifiedSource
