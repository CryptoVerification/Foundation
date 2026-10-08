import Foundation.Crypto.Semantics.Oracle.PacketResponseService

/-! Reuse a component's exact first-ready cost inside a continuing caller.
An ordinary termination certificate may include absorbing padding; this
additional hypothesis explicitly identifies its cost with first arrival. -/
namespace CryptoOracle.Interactive.PacketResponseService
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (H : Handler componentStep ready)

def Handler.ExactFirstReady : Prop :=
  (runToBoundary componentStep (fun component => (ready component).isSome)
    (H.execution.budget ()) (H.execution.entry ())).map
      (fun result => (H.read result.1, result.2)) = H.execution.costed ()

theorem body_costed_of_exact (hExact : H.ExactFirstReady) :
    (body componentStep begin ready hAbsorb code oracle caller state trace request H).costed () =
      H.execution.costed () := hExact

/-- A first-ready certificate supplies the service's unpadded joint cost. -/
theorem service_costed_of_exact (hExact : H.ExactFirstReady) :
    (service componentStep begin ready hAbsorb code oracle caller state trace request H).costed () =
      (H.execution.costed ()).map (fun result =>
        ((result.1.1, NativeCallback.resumed caller state trace request result.1.2),
          result.2 + (3 * result.1.2.length + 4))) := by
  rw [service_costed, body_costed_of_exact componentStep begin ready hAbsorb code oracle
    caller state trace request H hExact]

end CryptoOracle.Interactive.PacketResponseService
