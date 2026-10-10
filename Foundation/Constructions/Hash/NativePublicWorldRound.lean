import Foundation.Constructions.Hash.NativePublicWorldService
import Foundation.Constructions.Hash.NativePublicWorldPacket
import Foundation.Crypto.Semantics.Oracle.SourcePrefixExactTime
import Foundation.Crypto.Semantics.ProcedureInvariant
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! An actual source chooses the next request before a native world service
is selected. Supported format/length proofs certify that selection; they do
not execute a decoder or replace the source by a host continuation. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
open Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {n κ : Nat} (initial : Bits n) (terminal : Bits κ) (prior : List (List Bool × List Bool))
    {State : Type*} (callerCode : Code) (callerOracle : BitOracle State)

def nativeWorldSourceBoundary :
    PacketResponseSource.Control (NativeWorldComponent n κ) State (Configuration (IdealTable n κ)) → Bool
  | .source _ frame => SourcePrefix.boundary frame
  | _ => true

/-- The actual source runs until a request or genuine termination. Both
its chosen request and first-arrival cost remain independent of the cache. -/
noncomputable def nativeWorldSourcePrefix (saved : Configuration (IdealTable n κ)) :=
  SourcePrefix.liftTo callerCode callerOracle
    (nativeWorldCallerStep initial terminal prior callerCode callerOracle) nativeWorldSourceBoundary
    (PacketResponseSource.Control.source saved) (fun _ => rfl)
    (by intro frame active; cases hc : frame.control <;>
      simp_all [SourcePrefix.boundary, SourcePrefix.step, nativeWorldCallerStep, PacketResponseSource.step])

/-- Physical ownership transfer at the captured request. -/
noncomputable def nativeWorldAwaitTransfer (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : WorldInput (Bits κ) (Bits n)) :=
  Procedure.ofFixed (nativeWorldCallerStep initial terminal prior callerCode callerOracle)
    (fun _ : Unit => PacketResponseSource.Control.source saved
      ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩)
    (fun _ _ : Unit =>
      (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).entry ())
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp only [TimedExecution.eval, nativeWorldCaller_dispatch, PMF.pure_bind, PMF.pure_map]
      have entry : (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).entry () =
          .processing caller state trace (nativeWorldPacket request) (nativeWorldBegin saved (nativeWorldPacket request)) := by
        rw [nativeWorldService, PacketResponseService.service_entry, nativeWorldHandler_entry]
        cases request <;> simp only [nativeWorldBegin_hash, nativeWorldBegin_compression, cache]
      rw [entry])

noncomputable def nativeWorldWaitingService (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : WorldInput (Bits κ) (Bits n)) :=
  ((nativeWorldAwaitTransfer initial terminal prior callerCode callerOracle saved table cache caller state trace request).seq
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request)
    (fun _ middle _ => by cases middle; rfl)
    (fun _ => nativeWorldBudget request + (3 * n + 4))
    (fun _ _ _ => by rw [nativeWorldService_budget])).observe Prod.snd
      (fun _ output => PacketResponseSource.Control.source output.1 output.2)
      (fun _ output _ => by cases output with | mk middle output => cases middle; rfl)

theorem nativeWorldWaitingService_semantics (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : WorldInput (Bits κ) (Bits n)) :
    (nativeWorldWaitingService initial terminal prior callerCode callerOracle saved table cache caller state trace request).semantics () =
    (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).semantics () := by
  simp only [nativeWorldWaitingService, nativeWorldAwaitTransfer, Procedure.observe, Procedure.seq,
    TimedExecution.Procedure.ofFixed, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- This explicit supported-input condition must be proved from the caller
code. It does not assert that arbitrary raw requests terminate or decode. -/
def NativeWorldAdmissible (replyCap : Nat) (frame : Configuration State) : Prop :=
  ∀ caller raw, frame.control = .awaiting caller raw →
    ∃ request : WorldInput (Bits κ) (Bits n), nativeWorldPacket request = raw ∧
      nativeWorldBudget request + (3 * n + 4) ≤ replyCap

/-- Select the proof certificate for the request actually chosen by the
source. Classical choice here selects only a certificate for the unchanged
runtime entry, not a runtime parser or a different request. -/
noncomputable def nativeWorldResponse (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame}) :
    Procedure (nativeWorldCallerStep initial terminal prior callerCode callerOracle) Unit
      (Configuration (IdealTable n κ) × Configuration State) :=
  match hc : selected.val.control with
  | .awaiting caller raw =>
      let valid := selected.property caller raw hc
      nativeWorldWaitingService initial terminal prior callerCode callerOracle saved table cache
        caller selected.val.state selected.val.reverseTrace valid.choose
  | _ => Procedure.ofFixed _ (fun _ => .source saved selected.val) (fun _ output => .source output.1 output.2)
      (fun _ => PMF.pure (saved, selected.val)) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, PMF.pure_map])

/-- The certificate selection enters the exact preceding physical state. -/
theorem nativeWorldResponse_entry (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame}) :
    (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected).entry () =
      .source saved selected.val := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> try rfl
  case awaiting caller raw =>
    have format := (valid caller raw rfl).choose_spec.1
    change PacketResponseSource.Control.source saved ⟨state, .awaiting caller _, trace⟩ = _
    rw [format]

theorem nativeWorldResponse_exit (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame})
    (output : Configuration (IdealTable n κ) × Configuration State) :
    (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected).exit () output =
      .source output.1 output.2 := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> rfl

theorem nativeWorldResponse_budget (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame}) :
    (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected).budget () ≤ 1 + replyCap := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> try (change 0 ≤ _; omega)
  case awaiting caller raw =>
    have bound := (valid caller raw rfl).choose_spec.2
    change 1 + (nativeWorldBudget _ + (3 * n + 4)) ≤ _
    omega

/-- The source's actual first-arrival contract is operational independently
of the hidden compression cache. -/
theorem nativeWorldSourcePrefix_operational (saved : Configuration (IdealTable n κ)) :
    Procedure.Operational (nativeWorldSourcePrefix initial terminal prior callerCode callerOracle saved) := by
  unfold nativeWorldSourcePrefix SourcePrefix.liftTo
  apply Procedure.operational_liftBoundary

theorem nativeWorldWaitingService_operational (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : WorldInput (Bits κ) (Bits n)) :
    Procedure.Operational (nativeWorldWaitingService initial terminal prior callerCode callerOracle
      saved table cache caller state trace request) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_ofFixed
  · exact nativeWorldService_operational initial terminal prior callerCode callerOracle caller state trace table request

theorem nativeWorldResponse_operational (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame}) :
    Procedure.Operational (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected) := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> first
  | exact nativeWorldWaitingService_operational _ _ _ _ _ _ _ _ _ _ _ _
  | apply Procedure.operational_ofFixed; intro; simp [TimedExecution.eval, PMF.pure_map]

/-- Faithful packet encoding makes proof-certificate selection agree with
the typed request represented by the actual captured buffer. -/
theorem nativeWorldResponse_awaiting_semantics (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame})
    (caller : Machine.Configuration) (request : WorldInput (Bits κ) (Bits n))
    (captured : selected.val.control = .awaiting caller (nativeWorldPacket request)) :
    (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected).semantics () =
      (nativeWorldService initial terminal prior callerCode callerOracle caller selected.val.state
        selected.val.reverseTrace table request).semantics () := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  dsimp only at captured
  subst control
  have same : (valid caller (nativeWorldPacket request) rfl).choose = request :=
    nativeWorldPacket_injective (valid caller (nativeWorldPacket request) rfl).choose_spec.1
  change (nativeWorldWaitingService initial terminal prior callerCode callerOracle saved table cache
    caller state trace (valid caller (nativeWorldPacket request) rfl).choose).semantics () = _
  rw [nativeWorldWaitingService_semantics, same]

/-- Retained caches after a physical return are encodings of the same
real-world table distribution, rather than fresh independently sampled tables. -/
theorem nativeWorldService_cache_closed (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (table : CompressionTable (Bits κ) (Bits n))
    (request : WorldInput (Bits κ) (Bits n))
    (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((nativeWorldService initial terminal prior callerCode callerOracle
      caller state trace table request).semantics ()).support) :
    ∃ nextTable : CompressionTable (Bits κ) (Bits n), output.1.state = encodeCompressionTable nextTable := by
  have hm : (output.1.state, output.2) ∈
      (((nativeWorldService initial terminal prior callerCode callerOracle
        caller state trace table request).semantics ()).map (fun result => (result.1.state, result.2))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨output, hs, rfl⟩
  rw [nativeWorldService_packet, PMF.mem_support_map_iff] at hm
  obtain ⟨answer, _, he⟩ := hm
  exact ⟨answer.1, (congrArg Prod.fst he).symm⟩

theorem nativeWorldResponse_cache_closed (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (replyCap : Nat) (selected : {frame : Configuration State // NativeWorldAdmissible (n := n) (κ := κ) replyCap frame})
    (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap selected).semantics ()).support) :
    ∃ nextTable : CompressionTable (Bits κ) (Bits n), output.1.state = encodeCompressionTable nextTable := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> try {
    simp only [nativeWorldResponse, TimedExecution.Procedure.ofFixed, PMF.mem_support_pure_iff] at hs
    subst output
    exact ⟨table, cache⟩ }
  case awaiting caller raw =>
    change output ∈ ((nativeWorldWaitingService initial terminal prior callerCode callerOracle
      saved table cache caller state trace (valid caller raw rfl).choose).semantics ()).support at hs
    rw [nativeWorldWaitingService_semantics] at hs
    exact nativeWorldService_cache_closed initial terminal prior callerCode callerOracle _ _ _ _ _ output hs

section Round
variable (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, NativeWorldAdmissible (n := n) (κ := κ) replyCap frame)

/-- Attach format/length certificates to the request reached by the actual
source, preserving both its physical frame and first-arrival distribution. -/
noncomputable def nativeWorldCertifiedPrefix :=
  ((nativeWorldSourcePrefix initial terminal prior callerCode callerOracle saved).reindex
    (fun _ : Unit => selection)).certify (NativeWorldAdmissible (n := n) (κ := κ) replyCap)
      (fun _ frame hs => valid frame hs)

noncomputable def nativeWorldSourceCombined :=
  (nativeWorldCertifiedPrefix initial terminal prior callerCode callerOracle saved selection replyCap valid).seq
    (Procedure.dispatch (nativeWorldResponse initial terminal prior callerCode callerOracle saved table cache replyCap))
    (fun _ selected _ => nativeWorldResponse_entry initial terminal prior callerCode callerOracle saved table cache replyCap selected)
    (fun _ => 1 + replyCap)
    (fun _ selected _ => nativeWorldResponse_budget initial terminal prior callerCode callerOracle saved table cache replyCap selected)

/-- One actual source round, including selection, dispatch, native evaluation
and response loading. No machine state is normalized at the return. -/
noncomputable def nativeWorldSourceRound :=
  (nativeWorldSourceCombined initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).observe
    Prod.snd (fun _ output => PacketResponseSource.Control.source output.1 output.2)
    (fun _ output _ => (nativeWorldResponse_exit initial terminal prior callerCode callerOracle
      saved table cache replyCap output.1 output.2).symm)

theorem nativeWorldSourceRound_entry :
    (nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).entry () =
      .source saved selection.start := rfl

theorem nativeWorldSourceRound_exit (output : Configuration (IdealTable n κ) × Configuration State) :
    (nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).exit () output =
      .source output.1 output.2 := rfl

theorem nativeWorldSourceRound_budget :
    (nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).budget () =
      selection.budget + (1 + replyCap) := rfl

/-- Erasing proof data recovers exactly the source boundary distribution. -/
theorem nativeWorldCertifiedPrefix_erase :
    ((nativeWorldCertifiedPrefix initial terminal prior callerCode callerOracle saved selection replyCap valid).semantics ()).map
      Subtype.val = TimedExecution.eval (SourcePrefix.step callerCode callerOracle) selection.budget selection.start := by
  exact Procedure.certify_semantics _ _ _ ()

theorem nativeWorldSourceRound_semantics :
    (nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).semantics () =
      ((nativeWorldCertifiedPrefix initial terminal prior callerCode callerOracle saved selection replyCap valid).semantics ()).bind
        (fun selected => (nativeWorldResponse initial terminal prior callerCode callerOracle
          saved table cache replyCap selected).semantics ()) := by
  simp only [nativeWorldSourceRound, nativeWorldSourceCombined, Procedure.observe, Procedure.seq,
    Procedure.dispatch, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [show (fun x : Configuration (IdealTable n κ) × Configuration State => x) = id by rfl, PMF.map_id]

theorem nativeWorldSourceRound_operational :
    Procedure.Operational (nativeWorldSourceRound initial terminal prior callerCode callerOracle
      saved table cache selection replyCap valid) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_certify
    apply Procedure.operational_reindex
    exact nativeWorldSourcePrefix_operational initial terminal prior callerCode callerOracle saved
  · apply Procedure.operational_dispatch
    intro selected
    exact nativeWorldResponse_operational initial terminal prior callerCode callerOracle saved table cache replyCap selected
/-- Closure needed for the next adaptive source round concerns the actual
returned cache, including all entries accumulated in earlier calls. -/
theorem nativeWorldSourceRound_cache_closed (output : Configuration (IdealTable n κ) × Configuration State)
    (hs : output ∈ ((nativeWorldSourceRound initial terminal prior callerCode callerOracle
      saved table cache selection replyCap valid).semantics ()).support) :
    ∃ nextTable : CompressionTable (Bits κ) (Bits n), output.1.state = encodeCompressionTable nextTable := by
  rw [nativeWorldSourceRound_semantics, PMF.mem_support_bind_iff] at hs
  obtain ⟨selected, _, hs⟩ := hs
  exact nativeWorldResponse_cache_closed initial terminal prior callerCode callerOracle
    saved table cache replyCap selected output hs

/-- Resume the unchanged physical controller using the sum of actual
selection and response costs, not the sum of their worst-case bounds. -/
theorem nativeWorldSourceRound_law (horizon : Nat)
    (enough : selection.budget + (1 + replyCap) ≤ horizon) :
    TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle) horizon
      (.source saved selection.start) =
    ((nativeWorldSourceRound initial terminal prior callerCode callerOracle
      saved table cache selection replyCap valid).costed ()).bind
      (fun result => TimedExecution.eval (nativeWorldCallerStep initial terminal prior callerCode callerOracle)
        (horizon - result.2) (.source result.1.1 result.1.2)) :=
  (nativeWorldSourceRound initial terminal prior callerCode callerOracle
    saved table cache selection replyCap valid).law () horizon enough

/-- A deterministic captured frame may follow arbitrary proved native
preparation. Proof certification does not alter that frame's request. -/
theorem nativeWorldSourceRound_semantics_of_pure (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : WorldInput (Bits κ) (Bits n))
    (selectedPure : TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start = PMF.pure ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩) :
    (nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache selection replyCap valid).semantics () =
      (nativeWorldService initial terminal prior callerCode callerOracle caller state trace table request).semantics () := by
  let D := (nativeWorldCertifiedPrefix initial terminal prior callerCode callerOracle saved selection replyCap valid).semantics ()
  have erase : D.map Subtype.val = PMF.pure ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩ := by
    rw [nativeWorldCertifiedPrefix_erase, selectedPure]
  rw [nativeWorldSourceRound_semantics, ← PMF.bindOnSupport_eq_bind]
  change D.bindOnSupport _ = _
  trans D.bindOnSupport (fun _ _ => (nativeWorldService initial terminal prior callerCode callerOracle
    caller state trace table request).semantics ())
  · congr 1
    funext selected hs
    have selectedFrame : selected.val = ⟨state, .awaiting caller (nativeWorldPacket request), trace⟩ := by
      have hm : selected.val ∈ (D.map Subtype.val).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨selected, hs, rfl⟩
      rwa [erase, PMF.mem_support_pure_iff] at hm
    have captured : selected.val.control = .awaiting caller (nativeWorldPacket request) := by
      rw [selectedFrame]
    rw [nativeWorldResponse_awaiting_semantics initial terminal prior callerCode callerOracle
      saved table cache _ selected caller request captured, selectedFrame]
  · rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

end Round

section Capture
variable (machine : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : WorldInput (Bits κ) (Bits n)) (before after : List (Option Bool))
    (active : machine.halted = false) (call : callerCode[machine.pc]? = some .call)
    (packet : machine.outputTape = RequestExport.packetTape before after (nativeWorldPacket request))

/-- A concrete source prefix supplied by the existing native request-capture
proof. Completion is derived from the call instruction and actual output tape. -/
noncomputable def nativeWorldCaptureSelection : SourcePrefix.Input callerCode callerOracle where
  start := ⟨state, .running machine, trace⟩
  budget := 2 * (nativeWorldPacket request).length + 3
  complete := by
    intro frame hs
    rw [SourcePrefix.capture_run callerCode callerOracle machine state trace (nativeWorldPacket request)
      before after active call packet, PMF.mem_support_pure_iff] at hs
    subst frame
    rfl

/-- Format and response bounds for this actual selected request are derived,
not postulated as closure of all supported source returns. -/
theorem nativeWorldCaptureSelection_valid :
    ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      (nativeWorldCaptureSelection callerCode callerOracle machine state trace request before after active call packet).budget
      (nativeWorldCaptureSelection callerCode callerOracle machine state trace request before after active call packet).start).support,
      NativeWorldAdmissible (n := n) (κ := κ) (nativeWorldBudget request + (3 * n + 4)) frame := by
  intro frame hs
  change frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
    (2 * (nativeWorldPacket request).length + 3) ⟨state, .running machine, trace⟩).support at hs
  rw [SourcePrefix.capture_run callerCode callerOracle machine state trace (nativeWorldPacket request)
    before after active call packet, PMF.mem_support_pure_iff] at hs
  subst frame
  intro caller raw h
  cases h
  exact ⟨request, rfl, Nat.le_refl _⟩

/-- Exact first capture time and full caller frame, before any native service
is chosen. This is not padded to the source's analysis budget. -/
theorem nativeWorldCapturePrefix_costed (saved : Configuration (IdealTable n κ)) :
    (nativeWorldSourcePrefix initial terminal prior callerCode callerOracle saved).costed
      (nativeWorldCaptureSelection callerCode callerOracle machine state trace request before after active call packet) =
    PMF.pure (⟨state, .awaiting machine.advance (nativeWorldPacket request), trace⟩,
      2 * (nativeWorldPacket request).length + 3) := by
  change (runToBoundary (SourcePrefix.step callerCode callerOracle) SourcePrefix.boundary
    (2 * (nativeWorldPacket request).length + 3) ⟨state, .running machine, trace⟩).map
      (fun result => (result.1, result.2)) = _
  rw [SourcePrefix.capture_first_joint callerCode callerOracle machine state trace (nativeWorldPacket request)
    before after active call packet, PMF.pure_map]

noncomputable def nativeWorldCaptureRound (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table) :=
  nativeWorldSourceRound initial terminal prior callerCode callerOracle saved table cache
    (nativeWorldCaptureSelection callerCode callerOracle machine state trace request before after active call packet)
    (nativeWorldBudget request + (3 * n + 4))
    (nativeWorldCaptureSelection_valid callerCode callerOracle machine state trace request before after active call packet)

theorem nativeWorldCaptureRound_budget (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table) :
    (nativeWorldCaptureRound initial terminal prior callerCode callerOracle machine state trace request
      before after active call packet saved table cache).budget () =
      (2 * (nativeWorldPacket request).length + 3) + (1 + (nativeWorldBudget request + (3 * n + 4))) := rfl

theorem nativeWorldCaptureRound_operational (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table) :
    Procedure.Operational (nativeWorldCaptureRound initial terminal prior callerCode callerOracle machine state trace request
      before after active call packet saved table cache) :=
  nativeWorldSourceRound_operational _ _ _ _ _ _ _ _ _ _ _
/-- The concrete source capture followed by native evaluation has precisely
the physical service's output distribution. The source prefix neither changes
the requested message nor independently samples the private cache. -/
theorem nativeWorldCaptureRound_semantics (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table) :
    (nativeWorldCaptureRound initial terminal prior callerCode callerOracle machine state trace request
      before after active call packet saved table cache).semantics () =
    (nativeWorldService initial terminal prior callerCode callerOracle machine.advance state trace table request).semantics () := by
  apply nativeWorldSourceRound_semantics_of_pure
  exact SourcePrefix.capture_run callerCode callerOracle machine state trace (nativeWorldPacket request)
    before after active call packet

/-- Typed shared-world correspondence now includes the actual source
selection, not just a host-selected service call. -/
theorem nativeWorldCaptureRound_packet (saved : Configuration (IdealTable n κ))
    (table : CompressionTable (Bits κ) (Bits n)) (cache : saved.state = encodeCompressionTable table) :
    ((nativeWorldCaptureRound initial terminal prior callerCode callerOracle machine state trace request
      before after active call packet saved table cache).semantics ()).map (fun output => (output.1.state, output.2)) =
      (realWorld initial terminal table request).map (fun answer =>
        (encodeCompressionTable answer.1,
          NativeCallback.resumed machine.advance state trace (nativeWorldPacket request) answer.2.toList)) := by
  rw [nativeWorldCaptureRound_semantics, nativeWorldService_packet]

end Capture

end Foundation.Hash.Native
