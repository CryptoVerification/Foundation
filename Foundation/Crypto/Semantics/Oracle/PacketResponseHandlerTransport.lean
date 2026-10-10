import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime
import Foundation.Crypto.Semantics.ProcedureSimulation
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Embed an already proved physical packet handler in an exact dispatcher.
Every source step, returned saved frame, raw packet and genuine first-ready
cost is preserved. No runtime conversion is inserted by this proof. -/
namespace CryptoOracle.Interactive.PacketResponseService.Handler
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Source : Type u} {Target : Type v} {Saved : Type w}
    {sourceStep : Source → PMF Source} {sourceReady : Source → Option (Saved × List Bool)}
    (H : PacketResponseService.Handler sourceStep sourceReady)
    (targetStep : Target → PMF Target) (targetReady : Target → Option (Saved × List Bool))
    (embed : Source → Target)
    (hStep : ∀ state, targetStep (embed state) = (sourceStep state).map embed)
    (hReady : ∀ state, targetReady (embed state) = sourceReady state)
    (read : Target → Saved × List Bool) (hRead : ∀ state, read (embed state) = H.read state)

noncomputable def transport : PacketResponseService.Handler targetStep targetReady where
  execution := H.execution.transport targetStep embed hStep
  ready_exit output := by change targetReady (embed (H.execution.exit () output)) = _; rw [hReady, H.ready_exit]
  read := read
  read_exit output := by change read (embed (H.execution.exit () output)) = _; rw [hRead, H.read_exit]
  responseCap := H.responseCap
  response_bound := H.response_bound

/-- Exact first-ready cost survives the same dispatcher simulation. -/
theorem transport_exact (hExact : H.ExactFirstReady) :
    (transport H targetStep targetReady embed hStep hReady read hRead).ExactFirstReady := by
  change (runToBoundary targetStep (fun state => (targetReady state).isSome)
    (H.execution.budget ()) (embed (H.execution.entry ()))).map
      (fun result => (read result.1, result.2)) = H.execution.costed ()
  rw [runToBoundary_map sourceStep targetStep (fun state => (sourceReady state).isSome)
    (fun state => (targetReady state).isSome) embed
    (fun state => by rw [hReady]) (fun state _ => hStep state), PMF.map_comp]
  simpa only [ExactFirstReady, Function.comp_def, hRead] using hExact

/-- Reported dispatcher outputs are reached at their reported actual cost. -/
theorem transport_operational (hOperational : Procedure.Operational H.execution) :
    Procedure.Operational (transport H targetStep targetReady embed hStep hReady read hRead).execution := by
  intro input result support
  have h := hOperational input result support
  change embed (H.execution.exit input result.1) ∈
    (TimedExecution.eval targetStep result.2 (embed (H.execution.entry input))).support
  rw [← eval_map sourceStep targetStep embed (fun state => (hStep state).symm)]
  rw [PMF.mem_support_map_iff]
  exact ⟨_, h, rfl⟩

end CryptoOracle.Interactive.PacketResponseService.Handler
