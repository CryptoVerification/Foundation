import Foundation.Crypto.Semantics.Oracle.OneUseReturn
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Delivery of any physically written response preserves the use flag and
the private key. Successful and rejected requests share this contract. -/
namespace CryptoOracle.Interactive.OneUseDelivery
open Foundation.Probability TimedExecution
open OneUseSource
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
def packetMachine (packet : List Bool) : Machine.Configuration :=
  { outputTape := Machine.ResponseExport.endTape packet, halted := true }

noncomputable def packetReady : Machine.Procedure (List Bool) (List Bool) :=
  Machine.Procedure.ofFixed [] packetMachine (fun _ => packetMachine)
    PMF.pure (fun _ => 0) (fun _ => by simp [Machine.evalConfigWithin, PMF.pure_map])

def responseBoundary : OneUseSource.Control State → Bool
  | .handling _ _ _ _ _ (.calling _ _ (.responding component)) => NativeCallback.exportBoundary component
  | _ => true

def embedResponse (spent : Bool) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (frame : Machine.ResponseExport.Control × (Machine.Tape × Machine.Tape)) : OneUseSource.Control State :=
  .handling spent saved state trace request (.calling frame.2.1 frame.2.2 (.responding frame.1))

noncomputable def packetBody (first second : Machine.Tape) :=
  (((NativeCallback.exported packetReady id (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ machine => machine.outputTape.bits)
    (fun _ _ => by simp [packetReady, Machine.Procedure.ofFixed, Procedure.ofFixed,
      packetMachine, Machine.ResponseExport.endTape, Machine.Tape.bits, List.map_reverse])
    List.length (fun _ output h => by
      change output ∈ (PMF.pure _).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      exact Nat.le_refl _)).frame (Machine.Tape × Machine.Tape)).liftBoundary
    (fun frame => NativeCallback.exportBoundary frame.1) (fun _ _ _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, framedStep, Machine.ResponseExport.step, PMF.pure_map])
    (fun _ frame => NativeCallback.packetRead frame.1) (fun _ _ => rfl)
    (OneUseSource.step native code oracle) responseBoundary (embedResponse spent saved state trace request) (fun _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, OneUseSource.step, CheckedCallback.step,
        NativeCallback.step, embedResponse, framedStep, PMF.map_comp, Function.comp_def,
        packetReady, Machine.Procedure.ofFixed])).reindex
    (fun packet : List Bool => (packet, (first, second)))

noncomputable def reply (first second : Machine.Tape) :
    Procedure (OneUseSource.step native code oracle) (List Bool) Unit :=
  Procedure.ofFixed _
    (fun packet => .handling spent saved state trace request (.calling first second (.responding (.returned packet))))
    (fun packet _ => .source spent first (NativeCallback.resumed saved state trace request packet))
    (fun _ => PMF.pure ()) (fun packet => 3 * packet.length + 4)
    (fun packet => by simpa only [PMF.pure_map] using
      (OneUseSource.packet_return native code oracle spent saved state trace request first second packet))

noncomputable def packetDelivery (first second : Machine.Tape) :=
  (packetBody native code oracle spent saved state trace request first second).seq
    (reply native code oracle spent saved state trace request first second) (fun _ _ _ => rfl)
    (fun packet => 3 * packet.length + 4)
    (fun packet output h => by
      simp [packetBody, Procedure.reindex, Procedure.liftBoundary, Procedure.frame,
        NativeCallback.exported, packetReady, Machine.Procedure.ofFixed, Procedure.ofFixed,
        PMF.pure_map] at h
      subst output
      exact Nat.le_refl _)


theorem budget (first second : Machine.Tape) (packet : List Bool) :
    (packetDelivery native code oracle spent saved state trace request first second).budget packet =
      6 * packet.length + 8 := by
  change (0 + (3 * packet.length + 4)) + (3 * packet.length + 4) = _
  omega

theorem semantics (first second : Machine.Tape) (packet : List Bool) :
    (packetDelivery native code oracle spent saved state trace request first second).semantics packet =
      PMF.pure (packet, ()) := by
  simp [packetDelivery, packetBody, reply, NativeCallback.exported, packetReady, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.ofFixed, Procedure.liftBoundary, Procedure.frame, PMF.pure_map]

theorem distribution (first second : Machine.Tape) (packet : List Bool) :
    ((packetDelivery native code oracle spent saved state trace request first second).costed packet).map
      (fun result => (packetDelivery native code oracle spent saved state trace request first second).exit packet result.1) =
      PMF.pure (OneUseSource.Control.source spent first (NativeCallback.resumed saved state trace request packet)) := by
  have h := congrArg (fun distribution => distribution.map
    ((packetDelivery native code oracle spent saved state trace request first second).exit packet))
    ((packetDelivery native code oracle spent saved state trace request first second).correct packet)
  rw [semantics, PMF.pure_map] at h
  have he : (packetDelivery native code oracle spent saved state trace request first second).exit packet (packet, ()) =
      OneUseSource.Control.source spent first (NativeCallback.resumed saved state trace request packet) := by rfl
  rw [he] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

end CryptoOracle.Interactive.OneUseDelivery
