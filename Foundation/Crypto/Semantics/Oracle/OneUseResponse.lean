import Foundation.Crypto.Semantics.Oracle.OneUseDelivery
import Foundation.Crypto.Semantics.Oracle.CheckedResponse
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Physical tagging and delivery of arbitrary successful payloads in the
one-use outer controller. Contracts retain first-return costs and caller frames. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

def tagBoundary : Control State → Bool
  | .handling _ _ _ _ _ (.tagging _ _ (.returned _)) => true
  | .handling _ _ _ _ _ (.tagging _ _ _) => false
  | _ => true

def embedTag (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (frame : Machine.ResponsePacket.Control × (Machine.Tape × Machine.Tape)) : Control State :=
  .handling true saved state trace request (.tagging frame.2.1 frame.2.2 frame.1)

noncomputable def tagWriting (first second : Machine.Tape) :=
  (((Machine.ResponsePacket.procedure.frame (Machine.Tape × Machine.Tape)).liftBoundary
    (fun frame => match frame.1 with | .returned _ => true | _ => false)
    (fun _ _ _ => rfl)
    (fun frame h => by
      rcases frame with ⟨packet, retained⟩
      cases packet <;> simp_all [framedStep, Machine.ResponsePacket.step, PMF.pure_map])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step native code oracle) tagBoundary (embedTag saved state trace request) (fun frame => by rcases frame with ⟨packet, retained⟩; cases packet <;> rfl)
    (fun frame h => by
      rcases frame with ⟨packet, retained⟩
      cases packet <;> simp_all [step, CheckedCallback.step, embedTag, framedStep, PMF.map_comp, Function.comp_def])).reindex
    (fun payload : List Bool => (some payload, (first, second))))

def packetMachine := OneUseDelivery.packetMachine
noncomputable def packetReady := OneUseDelivery.packetReady
noncomputable def packetBody (first second : Machine.Tape) :=
  OneUseDelivery.packetBody native code oracle true saved state trace request first second
noncomputable def reply (first second : Machine.Tape) :=
  OneUseDelivery.reply native code oracle true saved state trace request first second
noncomputable def packetDelivery (first second : Machine.Tape) :=
  OneUseDelivery.packetDelivery native code oracle true saved state trace request first second

noncomputable def tagHandoff (first second : Machine.Tape) :
    Procedure (step native code oracle) (List Bool × Unit) Unit :=
  Procedure.ofFixed _
    (fun input => .handling true saved state trace request (.tagging first second (.returned
      (Machine.ResponseExport.endTape (Machine.ResponsePacket.codec.encode (some input.1))))))
    (fun input _ => .handling true saved state trace request (.calling first second (.responding (.running (packetMachine (true :: input.1))))))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by simp [TimedExecution.eval, step, CheckedCallback.step, packetMachine, OneUseDelivery.packetMachine, Machine.ResponsePacket.codec,
      Foundation.Encoding.optionBits, Foundation.Encoding.identity, PMF.pure_map])

noncomputable def tagged (first second : Machine.Tape) :=
  ((tagWriting native code oracle saved state trace request first second).remember.seq
    (tagHandoff native code oracle saved state trace request first second)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).seq
    ((packetDelivery native code oracle saved state trace request first second).reindex
      (fun result => true :: result.1.1)) (fun _ _ _ => rfl)
    (fun payload => 6 * payload.length + 14)
    (fun payload result h => by
      simp only [Procedure.seq, Procedure.remember, tagWriting, tagHandoff, Procedure.reindex,
        Procedure.liftBoundary, Procedure.frame, Machine.ResponsePacket.procedure, Procedure.ofFixed,
        PMF.pure_bind, PMF.pure_map, Function.comp_def] at h
      rw [PMF.mem_support_pure_iff] at h
      subst result
      simp only [packetDelivery, OneUseDelivery.packetDelivery, OneUseDelivery.packetBody, Procedure.reindex, Procedure.seq,
        Procedure.liftBoundary, Procedure.frame, NativeCallback.exported, OneUseDelivery.packetReady,
        Machine.Procedure.ofFixed, Procedure.ofFixed, Function.comp_def, List.length_cons]
      omega)

theorem tagged_budget (first second : Machine.Tape) (payload : List Bool) :
    (tagged native code oracle saved state trace request first second).budget payload = 8 * payload.length + 18 := by
  change (2 * payload.length + 3) + 1 + (6 * payload.length + 14) = _
  omega

theorem tagged_semantics (first second : Machine.Tape) (payload : List Bool) :
    (tagged native code oracle saved state trace request first second).semantics payload =
      PMF.pure (((payload, ()), ()), (true :: payload, ())) := by
  simp [tagged, tagWriting, tagHandoff, packetDelivery, OneUseDelivery.packetDelivery, OneUseDelivery.packetBody, OneUseDelivery.reply,
    NativeCallback.exported, OneUseDelivery.packetReady, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.remember, Procedure.reindex, Procedure.ofFixed,
    Procedure.liftBoundary, Procedure.frame, Machine.ResponsePacket.procedure, PMF.pure_map, Function.comp_def]

theorem tagged_distribution (first second : Machine.Tape) (payload : List Bool) :
    ((tagged native code oracle saved state trace request first second).costed payload).map
      (fun result => (tagged native code oracle saved state trace request first second).exit payload result.1) =
      PMF.pure (.source true first (NativeCallback.resumed saved state trace request (true :: payload))) := by
  have h := congrArg (fun distribution => distribution.map
    ((tagged native code oracle saved state trace request first second).exit payload))
    ((tagged native code oracle saved state trace request first second).correct payload)
  rw [tagged_semantics, PMF.pure_map] at h
  have he : (tagged native code oracle saved state trace request first second).exit payload
      (((payload, ()), ()), (true :: payload, ())) =
      .source true first (NativeCallback.resumed saved state trace request (true :: payload)) := by rfl
  rw [he] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

def rawBoundary : Control State → Bool
  | .handling _ _ _ _ _ (.computing _ _ component) => NativeCallback.exportBoundary component
  | _ => true

def embedRaw (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (frame : Machine.ResponseExport.Control × (Machine.Tape × Machine.Tape)) : Control State :=
  .handling true saved state trace request (.computing frame.2.1 frame.2.2 frame.1)

section Native
variable {Input : Type v} {Output : Type w}
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)

noncomputable def rawBody (first second : Machine.Tape) :=
  (((NativeCallback.exported P encode hHalt hTape read hRead cap hCap).frame
    (Machine.Tape × Machine.Tape)).liftBoundary (fun frame => NativeCallback.exportBoundary frame.1)
    (fun _ _ _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, framedStep, Machine.ResponseExport.step, PMF.pure_map])
    (fun _ frame => NativeCallback.packetRead frame.1) (fun _ _ => rfl)
    (step P.code code oracle) rawBoundary (embedRaw saved state trace request) (fun _ => rfl)
    (fun frame h => by
      rcases frame with ⟨component, retained⟩
      cases component <;> simp_all [NativeCallback.exportBoundary, step, CheckedCallback.step, embedRaw,
        framedStep, PMF.map_comp, Function.comp_def])).reindex
    (fun input : Input => (input, (first, second)))

noncomputable def rawHandoff (first second : Machine.Tape) :
    Procedure (step P.code code oracle) (Input × List Bool) Unit :=
  Procedure.ofFixed _ (fun input => .handling true saved state trace request (.computing first second (.returned input.2)))
    (fun input _ => .handling true saved state trace request (.tagging first second (.start (some input.2))))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, step, CheckedCallback.step, PMF.pure_map])

noncomputable def nativeResponse (first second : Machine.Tape) :=
  ((rawBody code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).remember.seq
    (rawHandoff code oracle saved state trace request P first second) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).seq
    ((tagged P.code code oracle saved state trace request first second).reindex (fun result => result.1.2))
    (fun _ _ _ => rfl) (fun input => 8 * cap input + 18)
    (fun input result hResult => by
      simp only [Procedure.seq, Procedure.remember, rawBody, Procedure.reindex,
        Procedure.liftBoundary, Procedure.frame, NativeCallback.exported, Procedure.ofFixed,
        rawHandoff, Function.comp_def] at hResult
      rw [PMF.mem_support_bind_iff] at hResult
      obtain ⟨middle, hMiddle, hMap⟩ := hResult
      rw [PMF.mem_support_map_iff] at hMiddle
      obtain ⟨packet, hPacket, he⟩ := hMiddle
      subst middle
      simp only [PMF.pure_map, PMF.mem_support_pure_iff] at hMap
      subst result
      rw [PMF.mem_support_map_iff] at hPacket
      obtain ⟨output, hOutput, he⟩ := hPacket
      subst packet
      change (tagged P.code code oracle saved state trace request first second).budget (encode output) ≤ _
      rw [tagged_budget]
      have h := hCap input output hOutput
      omega)

theorem nativeResponse_budget (first second : Machine.Tape) (input : Input) :
    (nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).budget input =
      P.execution.budget input + 11 * cap input + 23 := by
  change (P.execution.budget input + (3 * cap input + 4)) + 1 + (8 * cap input + 18) = _
  omega

def nativeResult (input : Input) (payload : List Bool) :=
  (((input, payload), ()), (((payload, ()), ()), (true :: payload, ())))

theorem nativeResponse_semantics (first second : Machine.Tape) (input : Input) :
    (nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).semantics input =
      (P.execution.semantics input).map (fun output => nativeResult input (encode output)) := by
  simp [nativeResponse, rawBody, rawHandoff, tagged_semantics, NativeCallback.exported,
    Procedure.seq, Procedure.remember, Procedure.reindex, Procedure.ofFixed,
    Procedure.liftBoundary, Procedure.frame, PMF.map, PMF.bind_bind, nativeResult, Function.comp_def]

theorem nativeResponse_distribution (first second : Machine.Tape) (input : Input) :
    ((nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).costed input).map
      (fun result => (nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).exit input result.1) =
      (P.execution.semantics input).map (fun output =>
        .source true first (NativeCallback.resumed saved state trace request (true :: encode output))) := by
  have h := congrArg (fun distribution => distribution.map
    ((nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).exit input))
    ((nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).correct input)
  rw [nativeResponse_semantics, PMF.map_comp] at h
  have he : ∀ output,
      (nativeResponse code oracle saved state trace request P encode hHalt hTape read hRead cap hCap first second).exit input
        (nativeResult input (encode output)) =
        .source true first (NativeCallback.resumed saved state trace request (true :: encode output)) := by
    intro output
    rfl
  simp only [PMF.map_comp, Function.comp_def] at h
  have hm := funext he
  rw [hm] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

end Native
end CryptoOracle.Interactive.OneUseSource
