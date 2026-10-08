import Foundation.Crypto.Semantics.Oracle.PacketResponseSource

/-! Reuse a proved raw-packet component inside a continuing caller.
The complete retained value and physical caller are returned. Every native
component duration, packet load and ownership transfer remains charged. -/
namespace CryptoOracle.Interactive.PacketResponseService
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}

structure Handler (componentStep : Component → PMF Component)
    (ready : Component → Option (Saved × List Bool)) where
  execution : Procedure componentStep Unit (Saved × List Bool)
  ready_exit : ∀ output, ready (execution.exit () output) = some output
  read : Component → Saved × List Bool
  read_exit : ∀ output, read (execution.exit () output) = output
  responseCap : Nat
  response_bound : ∀ output ∈ (execution.semantics ()).support, output.2.length ≤ responseCap

variable (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Saved × List Bool))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (H : Handler componentStep ready)

def boundary : PacketResponseSource.Control Component State Saved → Bool
  | .processing _ _ _ _ component => (ready component).isSome
  | _ => true

noncomputable def body :=
  H.execution.liftBoundary (fun component => (ready component).isSome)
    (fun _ output _ => by cases ‹Unit›; rw [H.ready_exit]; rfl)
    hAbsorb (fun _ => H.read) (fun unitArg output => by cases unitArg; exact H.read_exit output)
    (PacketResponseSource.step componentStep begin ready code oracle) (boundary ready)
    (PacketResponseSource.Control.processing caller state trace request)
    (fun _ => rfl) (fun component h => by
      cases hr : ready component with
      | none => simp [PacketResponseSource.step, hr]
      | some result => simp [hr] at h)

noncomputable def transfer : Procedure (PacketResponseSource.step componentStep begin ready code oracle)
    (Saved × List Bool) Unit :=
  Procedure.ofFixed _ (fun output => .processing caller state trace request (H.execution.exit () output))
    (fun output _ => .source output.1 (NativeCallback.resumed caller state trace request output.2))
    (fun _ => PMF.pure ()) (fun output => 3 * output.2.length + 4)
    (fun output => by
      simpa only [PMF.pure_map] using PacketResponseSource.return_run componentStep begin ready code oracle
        caller state trace request (H.execution.exit () output) output.1 output.2 (H.ready_exit output))

noncomputable def whole :=
  (body componentStep begin ready hAbsorb code oracle caller state trace request H).seq
    (transfer componentStep begin ready code oracle caller state trace request H)
    (fun _ _ _ => rfl) (fun _ => 3 * H.responseCap + 4)
    (fun _ output hOutput => by
      change output ∈ (H.execution.semantics ()).support at hOutput
      have h := H.response_bound output hOutput
      change 3 * output.2.length + 4 ≤ 3 * H.responseCap + 4
      omega)

noncomputable def service :=
  (whole componentStep begin ready hAbsorb code oracle caller state trace request H).observe
    (fun result => (result.1.1, NativeCallback.resumed caller state trace request result.1.2))
    (fun _ output => .source output.1 output.2) (fun _ _ _ => rfl)

theorem service_entry :
    (service componentStep begin ready hAbsorb code oracle caller state trace request H).entry () =
      .processing caller state trace request (H.execution.entry ()) := rfl

theorem service_budget :
    (service componentStep begin ready hAbsorb code oracle caller state trace request H).budget () =
      H.execution.budget () + (3 * H.responseCap + 4) := rfl

theorem service_semantics :
    (service componentStep begin ready hAbsorb code oracle caller state trace request H).semantics () =
      (H.execution.semantics ()).map (fun output =>
        (output.1, NativeCallback.resumed caller state trace request output.2)) := by
  simp only [service, whole, body, transfer, Procedure.observe, Procedure.seq, Procedure.liftBoundary,
    Procedure.ofFixed, PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  rfl

/-- The body records the actual first ready time, removing only absorbing
component padding. The returned packet controls the real loader duration. -/
theorem service_costed :
    (service componentStep begin ready hAbsorb code oracle caller state trace request H).costed () =
      ((body componentStep begin ready hAbsorb code oracle caller state trace request H).costed ()).map
        (fun result => ((result.1.1, NativeCallback.resumed caller state trace request result.1.2),
          result.2 + (3 * result.1.2.length + 4))) := by
  simp only [service, whole, transfer, Procedure.observe, Procedure.seq, Procedure.ofFixed,
    PMF.map_bind, PMF.pure_map, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- The caller continues after the actual service duration. An arbitrary
analysis horizon is never treated as the component's running time. -/
theorem service_law (horizon : Nat)
    (hTime : H.execution.budget () + (3 * H.responseCap + 4) ≤ horizon) :
    TimedExecution.eval (PacketResponseSource.step componentStep begin ready code oracle) horizon
      (.processing caller state trace request (H.execution.entry ())) =
      ((service componentStep begin ready hAbsorb code oracle caller state trace request H).costed ()).bind
        (fun result => TimedExecution.eval (PacketResponseSource.step componentStep begin ready code oracle)
          (horizon - result.2) (.source result.1.1 result.1.2)) :=
  (service componentStep begin ready hAbsorb code oracle caller state trace request H).law () horizon hTime

end CryptoOracle.Interactive.PacketResponseService
