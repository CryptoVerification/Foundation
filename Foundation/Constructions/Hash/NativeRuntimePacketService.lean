import Foundation.Constructions.Hash.NativeRuntimePacketExport
import Foundation.Crypto.Semantics.Oracle.PacketResponseService

/-! Concrete hash-to-caller service after request handoff. The entry explicitly
requires the hash's prepared input frame. This does not certify a free decoder,
input allocator, or whole adaptive caller; those launch obligations remain. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def runtimePacketHandler {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (input : RuntimeHashInput n κ) :
    PacketResponseService.Handler
      (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      NativePacketComponent.ready where
  execution := (runtimePacketProcedure initial terminal).reindex (fun _ : Unit => input)
  ready_exit _ := rfl
  read := NativePacketComponent.read
  read_exit _ := rfl
  responseCap := n
  response_bound := fun output support =>
    (runtimePacketProcedure_response_length initial terminal input output support).le

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (begin : Configuration (IdealTable n κ) → List Bool → NativePacketComponent.Control (IdealTable n κ))
    {State : Type*} (callerCode : Code) (callerOracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (input : RuntimeHashInput n κ)

/-- The existing packet service scans the physical hash tape, loads the caller
response, and releases that caller to execute its original next instruction. -/
noncomputable def runtimeHashService :=
  PacketResponseService.service
    (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
    begin NativePacketComponent.ready
    (NativePacketComponent.ready_absorbing _ _) callerCode callerOracle caller state trace request
    (runtimePacketHandler initial terminal input)

/-- Entry is an explicit physical precondition. No launch or packet-to-input
conversion is asserted by this theorem. -/
theorem runtimeHashService_entry :
    (runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).entry () =
      .processing caller state trace request
        (.computing (Configuration.initial (encodeCompressionTable input.1) (runtimeInputBits (input.2.map Bits.toList)))) := rfl

theorem runtimeHashService_budget :
    (runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).budget () =
      runtimeHashSteps n κ input.2.length + (5 * n + 9) := by
  rw [runtimeHashService, PacketResponseService.service_budget]
  change (runtimePacketProcedure initial terminal).budget input + (3 * n + 4) = _
  rw [runtimePacketProcedure_budget]
  omega

/-- Full native hash state and actual loaded caller are returned jointly.
The table in the retained frame is the same updated shared compression table. -/
theorem runtimeHashService_semantics :
    (runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).semantics () =
      (((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
        (typedHashFinish (runtimeHaltPc (3 * n) n κ) (runtimeFinalInput (input.2.map Bits.toList)))).map
          (fun frame => (frame, NativeCallback.resumed caller state trace request (runtimeExportPacket frame))) := by
  rw [runtimeHashService, PacketResponseService.service_semantics]
  change (((runtimePacketProcedure initial terminal).semantics input).map
    (fun output => (output.1, NativeCallback.resumed caller state trace request output.2))) = _
  rw [runtimePacketProcedure_semantics, PMF.map_comp]
  rfl

/-- Keep the genuine first-ready component time jointly with its private
state, then charge the real n-bit response loader and release transitions. -/
theorem runtimeHashService_costed :
    let H := runtimePacketHandler initial terminal input
    let body := PacketResponseService.body
      (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      begin NativePacketComponent.ready (NativePacketComponent.ready_absorbing _ _)
      callerCode callerOracle caller state trace request H
    (runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).costed () =
      (body.costed ()).map (fun result =>
        ((result.1.1, NativeCallback.resumed caller state trace request result.1.2), result.2 + (3 * n + 4))) := by
  dsimp only
  rw [runtimeHashService, PacketResponseService.service_costed]
  change ((PacketResponseService.body
      (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      begin NativePacketComponent.ready (NativePacketComponent.ready_absorbing _ _)
      callerCode callerOracle caller state trace request (runtimePacketHandler initial terminal input)).costed ()).bind _ =
    ((PacketResponseService.body
      (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      begin NativePacketComponent.ready (NativePacketComponent.ready_absorbing _ _)
      callerCode callerOracle caller state trace request (runtimePacketHandler initial terminal input)).costed ()).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  have h := (PacketResponseService.body
      (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
      begin NativePacketComponent.ready (NativePacketComponent.ready_absorbing _ _)
      callerCode callerOracle caller state trace request (runtimePacketHandler initial terminal input)).result_support () result hResult
  change result.1 ∈ ((runtimePacketProcedure initial terminal).semantics input).support at h
  simp only [Function.comp_def]
  rw [runtimePacketProcedure_response_length initial terminal input result.1 h]

/-- The residual law continues the real caller after service, retaining the
actual service cost and its dependence on the returned state. -/
theorem runtimeHashService_law (horizon : Nat)
    (enough : runtimeHashSteps n κ input.2.length + (5 * n + 9) ≤ horizon) :
    TimedExecution.eval
      (PacketResponseSource.step
        (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
        begin NativePacketComponent.ready callerCode callerOracle) horizon
      (.processing caller state trace request
        (.computing (Configuration.initial (encodeCompressionTable input.1) (runtimeInputBits (input.2.map Bits.toList))))) =
    ((runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).costed ()).bind
      (fun result => TimedExecution.eval
        (PacketResponseSource.step
          (NativePacketComponent.step (runtimeHashCode initial.toList terminal.toList) (idealCompression n κ))
          begin NativePacketComponent.ready callerCode callerOracle)
        (horizon - result.2) (.source result.1.1 result.1.2)) := by
  exact (runtimeHashService initial terminal begin callerCode callerOracle caller state trace request input).law
    () horizon (by rw [runtimeHashService_budget]; exact enough)

end Foundation.Hash.Native
