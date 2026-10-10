import Foundation.Constructions.Hash.NativeRuntimeRawPacket
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceOperational

/-! The raw-buffer native hash physically loads its returned tag into an
arbitrary caller and releases that caller's original continuation. The
compression cache is retained; the per-invocation compression trace starts
from the explicit fixed prior environment. No request decoder is executed
by begin: supported requests already have the proved runtime bit syntax. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def runtimeRawBegin {State : Type*} (saved : Configuration State) (request : List Bool) :
    NativePacketLaunch.Control State := .preparing saved.state (.loading request {})

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool))
    {State : Type*} (callerCode : Code) (callerOracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (input : RuntimeHashInput n κ)

noncomputable def runtimeRawHashService :=
  PacketResponseService.service
    (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
    runtimeRawBegin runtimeRawReady (runtimeRawReady_absorbing _ _ prior)
    callerCode callerOracle caller state trace request (runtimeRawPacketHandler initial terminal prior input)

theorem runtimeRawHashService_entry :
    (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).entry () =
    .processing caller state trace request
      (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {})) := rfl

/-- Raw loading, copying, hashing, physical export and caller response
loading are all charged. The caller's future instructions are separate. -/
theorem runtimeRawHashService_budget :
    (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).budget () =
    runtimeRawExportSteps n κ input.2.length + (3 * n + 4) := rfl

/-- The retained private frame and the actual resumed caller are returned
jointly, including the complete updated compression table. -/
theorem runtimeRawHashService_semantics :
    (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).semantics () =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ input.2.length)
      (runtimeTransferStart input.1 input.2 prior)).map (fun result =>
        (result.1, NativeCallback.resumed caller state trace request (runtimeExportPacket result.1))) := by
  rw [runtimeRawHashService, PacketResponseService.service_semantics]
  change ((runtimeRawPacketProcedure initial terminal prior).semantics input).map _ = _
  rw [runtimeRawPacketProcedure_semantics, PMF.map_comp]
  rfl

/-- Joint real service cost, updated private frame and physically resumed
caller. Response loading costs exactly 3n+4 more than physical tag return. -/
theorem runtimeRawHashService_costed :
    (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).costed () =
    (runToBoundary
      (Reification.timedStep (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ))
      (fun frame => Reification.terminal frame.control) (runtimeLinkedHashSteps n κ input.2.length)
      (runtimeTransferStart input.1 input.2 prior)).map (fun result =>
        ((result.1, NativeCallback.resumed caller state trace request (runtimeExportPacket result.1)),
          runtimePreparationSteps κ input.2.length + result.2 + (2 * n + 5) + (3 * n + 4))) := by
  rw [runtimeRawHashService, PacketResponseService.service_costed_of_exact _ _ _ _ _ _ _ _ _ _ _
    (runtimeRawPacketHandler_exact initial terminal prior input)]
  change ((runtimeRawPacketProcedure initial terminal prior).costed input).map _ = _
  rw [runtimeRawPacketProcedure_costed, PMF.map_comp]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result support
  have length := (runtime_linked_first_cell_exportable initial terminal input.2 input.1 prior result support).2.2.2
  dsimp only [Function.comp_def]
  rw [length]

theorem runtimeRawHashService_operational :
    Procedure.Operational
      (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input) := by
  apply PacketResponseService.service_operational

/-- The updated compression table, full per-invocation trace and returned
tag in the service have exactly the original typed-hash distribution. -/
theorem runtimeRawHashService_packet :
    ((runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).semantics ()).map
      (fun output => some (CellEquivalence.packetObservation output.1)) =
    ((Foundation.Hash.prefixFreeMD initial terminal input.2).run RandomOracle.oracle input.1).map
      (fun out => some (some out.result.toList, encodeCompressionTable out.state,
        (out.trace.map (fun e => (compressionPacket e.1, e.2.toList))).reverse ++ prior)) := by
  rw [runtimeRawHashService_semantics, PMF.map_comp]
  have h := congrArg (fun distribution => distribution.map some)
    (linked_hash_stopped_observation initial terminal input.2 input.1 prior)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- The same packet service continues the caller at its original next
instruction, using the actual branch-dependent service cost. -/
theorem runtimeRawHashService_law (horizon : Nat)
    (enough : runtimeRawExportSteps n κ input.2.length + (3 * n + 4) ≤ horizon) :
    TimedExecution.eval
      (PacketResponseSource.step
        (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
        runtimeRawBegin runtimeRawReady callerCode callerOracle) horizon
      (.processing caller state trace request
        (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {}))) =
    ((runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).costed ()).bind
      (fun result => TimedExecution.eval
        (PacketResponseSource.step
          (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
          runtimeRawBegin runtimeRawReady callerCode callerOracle)
        (horizon - result.2) (.source result.1.1 result.1.2)) := by
  exact (runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).law
    () horizon enough

/-- Starting at an actual suspended oracle call also charges the dispatch
transition. The request is passed unchanged to the physical raw loader. -/
theorem runtimeRawHashService_from_awaiting (saved : Configuration (IdealTable n κ))
    (cache : saved.state = encodeCompressionTable input.1)
    (request_format : request = runtimeInputBits (input.2.map Bits.toList)) (horizon : Nat)
    (enough : 1 + (runtimeRawExportSteps n κ input.2.length + (3 * n + 4)) ≤ horizon) :
    TimedExecution.eval
      (PacketResponseSource.step
        (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
        runtimeRawBegin runtimeRawReady callerCode callerOracle) horizon
      (.source saved ⟨state, .awaiting caller request, trace⟩) =
    ((runtimeRawHashService initial terminal prior callerCode callerOracle caller state trace request input).costed ()).bind
      (fun result => TimedExecution.eval
        (PacketResponseSource.step
          (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
          runtimeRawBegin runtimeRawReady callerCode callerOracle)
        (horizon - (1 + result.2)) (.source result.1.1 result.1.2)) := by
  have first : TimedExecution.eval
      (PacketResponseSource.step
        (NativePacketLaunch.step (runtimeLinkedHashCode initial.toList terminal.toList) (idealCompression n κ) false prior)
        runtimeRawBegin runtimeRawReady callerCode callerOracle) 1
      (.source saved ⟨state, .awaiting caller request, trace⟩) =
      PMF.pure (.processing caller state trace request
        (.preparing (encodeCompressionTable input.1) (.loading (runtimeInputBits (input.2.map Bits.toList)) {}))) := by
    simp [TimedExecution.eval, PacketResponseSource.step, runtimeRawBegin, cache, request_format]
  rw [show horizon = 1 + (horizon - 1) by omega, eval_add, first, PMF.pure_bind,
    runtimeRawHashService_law initial terminal prior callerCode callerOracle caller state trace request input
      (horizon - 1) (by omega)]
  simp only [Nat.sub_sub]
  congr 1
  funext result
  congr 1
  omega

end Foundation.Hash.Native
