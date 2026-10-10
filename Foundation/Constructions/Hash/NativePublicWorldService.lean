import Foundation.Constructions.Hash.NativePublicWorld
import Foundation.Constructions.Hash.NativePublicCompressionProcedure
import Foundation.Crypto.Semantics.Oracle.PacketResponseHandlerTransport

/-! Both concrete physical windows return through the same existing caller
service. The returned native frame retains the shared updated cache, and the
source response tape is populated before its original continuation resumes. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ)
    (prior : List (List Bool × List Bool))

def nativeWorldPacketRead : NativeWorldComponent n κ → Configuration (IdealTable n κ) × List Bool
  | .inl component => runtimeRawRead component
  | .inr component => runtimeRawRead component

noncomputable def nativeWorldHandler (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    PacketResponseService.Handler (nativeWorldStep initial terminal prior) nativeWorldReady :=
  match request with
  | .inl message =>
      PacketResponseService.Handler.transport (runtimeRawPacketHandler initial terminal prior (table, message))
        (nativeWorldStep initial terminal prior) nativeWorldReady Sum.inl (fun _ => rfl) (fun _ => rfl)
        nativeWorldPacketRead (fun _ => rfl)
  | .inr input =>
      PacketResponseService.Handler.transport (publicCompressionPacketHandler prior (table, input))
        (nativeWorldStep initial terminal prior) nativeWorldReady Sum.inr (fun _ => rfl) (fun _ => rfl)
        nativeWorldPacketRead (fun _ => rfl)

theorem nativeWorldHandler_exact (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    (nativeWorldHandler initial terminal prior table request).ExactFirstReady := by
  cases request with
  | inl message =>
      exact PacketResponseService.Handler.transport_exact _ _ _ Sum.inl
        (fun _ => rfl) (fun _ => rfl) nativeWorldPacketRead (fun _ => rfl)
        (runtimeRawPacketHandler_exact initial terminal prior (table, message))
  | inr input =>
      exact PacketResponseService.Handler.transport_exact _ _ _ Sum.inr
        (fun _ => rfl) (fun _ => rfl) nativeWorldPacketRead (fun _ => rfl)
        (publicCompressionPacketHandler_exact prior (table, input))

theorem nativeWorldHandler_entry (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    (nativeWorldHandler initial terminal prior table request).execution.entry () =
    nativeWorldBegin ⟨encodeCompressionTable table, .finished false, prior⟩ (nativeWorldPacket request) := by
  cases request <;> rfl

theorem nativeWorldHandler_budget (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    (nativeWorldHandler initial terminal prior table request).execution.budget () = nativeWorldBudget request := by
  cases request <;> rfl

theorem nativeWorldHandler_responseCap (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    (nativeWorldHandler initial terminal prior table request).responseCap = n := by
  cases request <;> rfl

/-- The physical handler's updated cache and actual packet are precisely
those used in the proved adaptive block semantics. -/
theorem nativeWorldHandler_packet (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n)) :
    ((nativeWorldHandler initial terminal prior table request).execution.semantics ()).map
      (fun output => (output.1.state, output.2)) =
    nativeWorldOracle initial terminal prior (encodeCompressionTable table) request := by
  let H := nativeWorldHandler initial terminal prior table request
  have run := H.execution.final_run ()
    (fun output _ => nativeWorld_ready_absorbing initial terminal prior _ (by rw [H.ready_exit]; rfl))
    (H.execution.budget ()) (Nat.le_refl _)
  rw [nativeWorldOracle, ← nativeWorldHandler_entry initial terminal prior table request,
    ← nativeWorldHandler_budget initial terminal prior table request, run, PMF.map_comp]
  cases request <;> rfl

variable {State : Type*} (callerCode : Code) (callerOracle : BitOracle State)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (table : CompressionTable (Bits κ) (Bits n)) (request : WorldInput (Bits κ) (Bits n))

noncomputable def nativeWorldService :=
  PacketResponseService.service (nativeWorldStep initial terminal prior) nativeWorldBegin nativeWorldReady
    (nativeWorld_ready_absorbing initial terminal prior) callerCode callerOracle
    caller state trace (nativeWorldPacket request) (nativeWorldHandler initial terminal prior table request)

theorem nativeWorldService_exit (output : Configuration (IdealTable n κ) × Configuration State) :
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).exit () output =
      .source output.1 output.2 := rfl

theorem nativeWorldService_budget :
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).budget () =
      nativeWorldBudget request + (3 * n + 4) := by
  rw [nativeWorldService, PacketResponseService.service_budget,
    nativeWorldHandler_budget, nativeWorldHandler_responseCap]

/-- Exact first component return followed by actual cell-by-cell source
response loading; the full saved frame and actual source continuation remain. -/
theorem nativeWorldService_costed :
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).costed () =
    ((nativeWorldHandler initial terminal prior table request).execution.costed ()).map
      (fun result =>
        ((result.1.1, NativeCallback.resumed caller state trace (nativeWorldPacket request) result.1.2),
          result.2 + (3 * result.1.2.length + 4))) := by
  apply PacketResponseService.service_costed_of_exact
  exact nativeWorldHandler_exact initial terminal prior table request

/-- This is actual reachability at the reported cost, not only a law for
spending an analysis horizon after a hypothetical return. -/
theorem nativeWorldService_operational :
    Procedure.Operational
      (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request) := by
  apply PacketResponseService.service_operational

/-- The actual resumed caller and actual retained cache have the shared
real-world distribution. The packet is already physically loaded on return. -/
theorem nativeWorldService_packet :
    ((nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).semantics ()).map
      (fun output => (output.1.state, output.2)) =
    (realWorld initial terminal table request).map (fun answer =>
      (encodeCompressionTable answer.1,
        NativeCallback.resumed caller state trace (nativeWorldPacket request) answer.2.toList)) := by
  rw [nativeWorldService, PacketResponseService.service_semantics, PMF.map_comp]
  have h := congrArg (fun distribution => distribution.map (fun output : IdealTable n κ × List Bool =>
    (output.1, NativeCallback.resumed caller state trace (nativeWorldPacket request) output.2)))
    (nativeWorldHandler_packet initial terminal prior table request)
  rw [nativeWorldOracle_step] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Continue the unchanged two-window controller after the actual service
cost. The physical response boundary does not terminate the whole caller. -/
theorem nativeWorldService_law (horizon : Nat)
    (enough : nativeWorldBudget request + (3 * n + 4) ≤ horizon) :
    TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle) horizon
      (.processing caller state trace (nativeWorldPacket request)
        (nativeWorldBegin ⟨encodeCompressionTable table, .finished false, prior⟩ (nativeWorldPacket request))) =
    ((nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).costed ()).bind
      (fun result => TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle)
        (horizon - result.2) (.source result.1.1 result.1.2)) := by
  have h := (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).law
    () horizon (by rw [nativeWorldService_budget]; exact enough)
  simp only [nativeWorldService_exit] at h
  simpa only [nativeWorldService, PacketResponseService.service_entry,
    nativeWorldHandler_entry, nativeWorldCallerStep] using h

/-- Charge the initial dispatch of the actual waiting caller. Its retained
cache is the previous window's actual output; other saved frame fields are
not normalized or replaced by the proof-side input representation. -/
theorem nativeWorldService_from_awaiting (saved : Configuration (IdealTable n κ))
    (cache : saved.state = encodeCompressionTable table) (horizon : Nat)
    (enough : 1 + (nativeWorldBudget request + (3 * n + 4)) ≤ horizon) :
    TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle) horizon
      (.source saved ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩) =
    ((nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).costed ()).bind
      (fun result => TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle)
        (horizon - (1 + result.2)) (.source result.1.1 result.1.2)) := by
  have first : TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle) 1
      (.source saved ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩) =
      PMF.pure (.processing caller state trace (nativeWorldPacket request)
        (nativeWorldBegin ⟨encodeCompressionTable table, .finished false, prior⟩ (nativeWorldPacket request))) := by
    have entry : nativeWorldBegin saved (nativeWorldPacket request) =
        nativeWorldBegin ⟨encodeCompressionTable table, .finished false, prior⟩ (nativeWorldPacket request) := by
      cases request <;> simp only [nativeWorldBegin_hash, nativeWorldBegin_compression, cache]
    simp only [TimedExecution.eval, nativeWorldCaller_dispatch, PMF.pure_bind, entry]
  rw [show horizon = 1 + (horizon - 1) by omega, eval_add, first, PMF.pure_bind,
    nativeWorldService_law initial terminal prior callerCode callerOracle caller state trace table request
      (horizon - 1) (by omega)]
  simp only [Nat.sub_sub]
  congr 1
  funext result
  congr 1
  omega

/-- Public compression's true service cost is constant at these widths;
loading the caller's response is charged after the first physical return. -/
theorem nativeWorldService_compression_costed (input : CompressionInput (Bits κ) (Bits n)) :
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table (.inr input)).costed () =
    (RandomOracle.oracle table input).map (fun answer =>
      ((NativeCompressionCall.finish (compressionPacket input) prior
          (encodeCompressionTable answer.1, answer.2.toList),
        NativeCallback.resumed caller state trace (nativeWorldPacket (.inr input)) answer.2.toList),
        NativeCompressionCall.rawSteps (n + κ + 1) n + (3 * n + 4))) := by
  rw [nativeWorldService_costed]
  simp only [nativeWorldHandler, PacketResponseService.Handler.transport, Procedure.transport,
    publicCompressionPacketHandler, publicCompressionPacketProcedure, Procedure.reindex,
    TimedExecution.Procedure.ofFixed, PMF.map_comp, Function.comp_def, Bits.length_toList]

end Foundation.Hash.Native