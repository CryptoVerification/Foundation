import Foundation.Crypto.Semantics.Oracle.ReusableResponseReturn
import Foundation.Crypto.Semantics.Oracle.RetainedResponseDelivery

/-! Export an existing halted physical output, load the response and release
the caller inside the reusable runtime. Actual export duration is retained. -/
namespace CryptoOracle.Interactive.ReusableResponseDelivery
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (retained : Saved) (input : RetainedResponseDelivery.Input)

noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

def boundary : ReusableResponseSource.Control Component State Saved → Bool
  | .calling _ _ _ _ (.responding component) _ => NativeCallback.exportBoundary component
  | _ => true

noncomputable def exported :=
  (NativeCallback.exported (RetainedResponseDelivery.ready native input) (fun _ => input.packet)
    (fun _ _ => input.halted) (fun _ _ => input.layout)
    (fun _ _ => ()) (fun _ _ => rfl) (fun _ => input.packet.length) (fun _ _ _ => Nat.le_refl _)).liftBoundary
    NativeCallback.exportBoundary (fun _ _ _ => rfl)
    (fun component h => by cases component <;> simp_all [NativeCallback.exportBoundary, Machine.ResponseExport.step])
    (fun _ => NativeCallback.packetRead) (fun _ _ => rfl)
    (outerStep componentStep begin ready native code oracle) boundary
    (fun component => .calling caller state trace request (.responding component) retained)
    (fun _ => rfl)
    (fun component h => by cases component <;>
      simp_all [NativeCallback.exportBoundary, outerStep, ReusableResponseSource.step, NativeCallback.step,
        PMF.map_comp, Function.comp_def, RetainedResponseDelivery.ready, Machine.Procedure.ofFixed])

theorem exported_semantics (argument : Unit) :
    (exported componentStep begin ready native code oracle caller state trace request retained input).semantics argument =
      PMF.pure input.packet := by
  simp [exported, Procedure.liftBoundary, NativeCallback.exported, RetainedResponseDelivery.ready,
    Machine.Procedure.ofFixed, Procedure.ofFixed, PMF.pure_map]

noncomputable def whole :=
  (exported componentStep begin ready native code oracle caller state trace request retained input).seq
    (ReusableResponseReturn.procedure componentStep begin ready native code oracle caller state trace request retained)
    (fun _ _ _ => rfl) (fun _ => 3 * input.packet.length + 4)
    (fun _ packet h => by
      rw [exported_semantics] at h
      rw [PMF.mem_support_pure_iff] at h
      subst packet
      exact Nat.le_refl _)

theorem budget :
    (whole componentStep begin ready native code oracle caller state trace request retained input).budget () =
      6 * input.packet.length + 8 := by
  change (0 + (3 * input.packet.length + 4)) + (3 * input.packet.length + 4) = _
  omega

theorem semantics :
    (whole componentStep begin ready native code oracle caller state trace request retained input).semantics () =
      PMF.pure (input.packet, ()) := by
  change ((exported componentStep begin ready native code oracle caller state trace request retained input).semantics ()).bind
    (fun packet => (PMF.pure ()).map (fun result => (packet, result))) = _
  rw [exported_semantics]
  simp only [PMF.pure_bind, PMF.pure_map]

theorem law (horizon : Nat) (hBudget : 6 * input.packet.length + 8 ≤ horizon) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) horizon
      (.calling caller state trace request (.responding (.running input.machine)) retained) =
      ((whole componentStep begin ready native code oracle caller state trace request retained input).costed ()).bind
        (fun result => TimedExecution.eval (outerStep componentStep begin ready native code oracle) (horizon - result.2)
          (.source retained (NativeCallback.resumed caller state trace request result.1.1))) := by
  exact (whole componentStep begin ready native code oracle caller state trace request retained input).law () horizon
    (by rw [budget]; exact hBudget)

end CryptoOracle.Interactive.ReusableResponseDelivery
