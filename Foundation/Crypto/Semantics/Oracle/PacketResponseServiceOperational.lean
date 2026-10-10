import Foundation.Crypto.Semantics.Oracle.PacketResponseService
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! Every reported packet service result is reached by the original caller
runtime at its reported actual cost. Boundary lifting, physical loading and
the existing execution-contract composition supply the operational proof. -/
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

theorem body_operational :
    Procedure.Operational (body componentStep begin ready hAbsorb code oracle caller state trace request H) := by
  apply Procedure.operational_liftBoundary

theorem transfer_operational :
    Procedure.Operational (transfer componentStep begin ready code oracle caller state trace request H) := by
  apply Procedure.operational_ofFixed

theorem service_operational :
    Procedure.Operational (service componentStep begin ready hAbsorb code oracle caller state trace request H) := by
  unfold service
  apply Procedure.operational_observe
  unfold whole
  apply Procedure.operational_seq
  · exact body_operational componentStep begin ready hAbsorb code oracle caller state trace request H
  · exact transfer_operational componentStep begin ready code oracle caller state trace request H

end CryptoOracle.Interactive.PacketResponseService
