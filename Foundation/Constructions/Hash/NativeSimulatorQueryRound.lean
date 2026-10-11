import Foundation.Constructions.Hash.NativeSimulatorQueryService
import Foundation.Crypto.Semantics.Oracle.SourcePrefixExactTime
import Foundation.Crypto.Semantics.ProcedureInvariant
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! One actual source round for the simulator window: the caller captures
its next raw request, the concrete native component evaluates it against
the retained private table, and the response is loaded into the caller.
The retained frame keeps the private table at the head of its input tape,
so the same controller can serve the next request. -/
namespace Foundation.Hash.Native.SimulatorQueryRound
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The retained simulator frame together with the private compression
table physically stored at the head of its input tape. -/
structure Retained (n κ : Nat) (State : Type) where
  table : CompressionTable (Bits κ) (Bits n)
  saved : Configuration State
  machine : Machine.Configuration
  hControl : saved.control = .running machine
  tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table))

variable {n κ : Nat} {State Source : Type}

/-- The continuing caller step with the concrete simulator component. -/
noncomputable def callerStep (n κ : Nat) (oracle : BitOracle State) (callerCode : Code)
    (callerOracle : BitOracle Source) :
    PacketResponseSource.Control (SimulatorQueryPacket.Control State) Source (Configuration State) →
      PMF (PacketResponseSource.Control (SimulatorQueryPacket.Control State) Source (Configuration State)) :=
  PacketResponseSource.step (SimulatorQueryPacket.step n κ oracle) SimulatorQueryService.beginRound
    SimulatorQueryPacket.ready callerCode callerOracle

/-- The boundary of the captured request, reused from the source prefix. -/
def simulatorSourceBoundary (_saved : Configuration State) : PacketResponseSource.Control
    (SimulatorQueryPacket.Control State) Source (Configuration State) → Bool
  | .source _ frame => SourcePrefix.boundary frame
  | _ => true

/-- The actual source runs until a request or genuine termination. Both its
chosen request and first-arrival cost stay in the captured physical frame. -/
noncomputable def simulatorSourcePrefix (oracle : BitOracle State) (callerCode : Code)
    (callerOracle : BitOracle Source) (ret : Retained n κ State) :
    Procedure (callerStep n κ oracle callerCode callerOracle)
      (SourcePrefix.Input callerCode callerOracle) (Configuration Source) :=
  SourcePrefix.liftTo callerCode callerOracle (callerStep n κ oracle callerCode callerOracle)
    (simulatorSourceBoundary ret.saved)
    (fun frame => PacketResponseSource.Control.source ret.saved frame)
    (fun _ => rfl)
    (by
      intro frame active
      cases hc : frame.control <;>
        simp_all [SourcePrefix.boundary, SourcePrefix.step, callerStep, PacketResponseSource.step])

/-- Physical ownership transfer from the captured request to the component.
The private table is neither rebuilt nor normalized here. -/
noncomputable def simulatorAwaitTransfer (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) :
    TimedExecution.Procedure (callerStep n κ oracle callerCode callerOracle) Unit Unit :=
  TimedExecution.Procedure.ofFixed (callerStep n κ oracle callerCode callerOracle)
    (fun _ : Unit => PacketResponseSource.Control.source ret.saved
      ⟨callerState, .awaiting caller (compressionPacket query ++ [false]), callerTrace⟩)
    (fun _ _ : Unit =>
      (SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace query
        ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
        (compressionPacket query ++ [false])).entry ())
    (fun _ => PMF.pure ()) (fun _ => 1)
    (by
      intro _
      simp only [TimedExecution.eval, callerStep, PacketResponseSource.step, PMF.pure_bind, PMF.pure_map,
        SimulatorQueryService.beginRound, SimulatorQueryService.retainedMachine, ret.hControl]
      rfl)

noncomputable def simulatorWaitingService (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) :
    TimedExecution.Procedure (callerStep n κ oracle callerCode callerOracle) Unit
      (Configuration State × Configuration Source) :=
  ((simulatorAwaitTransfer oracle positive callerCode callerOracle ret caller callerState callerTrace query).seq
    (SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace query
      ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
      (compressionPacket query ++ [false]))
    (fun _ middle _ => by cases middle; rfl)
    (fun _ => SimulatorQueryPacket.steps query ret.table + (3 * n + 4))
    (fun _ _ _ => by
      rw [SimulatorQueryService.simulatorService_budget oracle ret.table ret.saved.state ret.machine
        ret.saved.reverseTrace query ret.tableLayout positive callerCode callerOracle caller callerState
        callerTrace (compressionPacket query ++ [false])])).observe Prod.snd
    (fun _ output => PacketResponseSource.Control.source output.1 output.2)
    (fun _ output _ => by cases output with | mk middle output => cases middle; rfl)

theorem simulatorWaitingService_semantics (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) :
    (simulatorWaitingService oracle positive callerCode callerOracle ret caller callerState callerTrace
      query).semantics () =
    (SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace query
      ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
      (compressionPacket query ++ [false])).semantics () := by
  simp only [simulatorWaitingService, simulatorAwaitTransfer, Procedure.observe, Procedure.seq,
    TimedExecution.Procedure.ofFixed, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- The raw packet determines the typed compression input. -/
theorem compressionPacket_injective (n κ : Nat) : Function.Injective (@compressionPacket n κ) := by
  intro left right equal
  apply compressionKey_injective n κ
  have h := congrArg (fun p => (fixedBits (n + κ + 1)).decode p) equal
  rw [compressionKey_decode left, compressionKey_decode right] at h
  exact Option.some_inj.mp h

/-- This explicit supported-input condition must be proved from the caller
code. It does not assert that arbitrary raw requests terminate or decode. -/
def SimulatorAdmissible (table : CompressionTable (Bits κ) (Bits n)) (replyCap : Nat)
    (frame : Configuration Source) : Prop :=
  ∀ caller raw, frame.control = .awaiting caller raw →
    ∃ query : CompressionInput (Bits κ) (Bits n), raw = compressionPacket query ++ [false] ∧
      SimulatorQueryPacket.steps query table + (3 * n + 4) ≤ replyCap

/-- Select the proof certificate for the request actually chosen by the
source. Classical choice here selects only a certificate for the unchanged
runtime entry, not a runtime parser or a different request. -/
noncomputable def simulatorResponse (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (replyCap : Nat)
    (selected : {frame : Configuration Source // SimulatorAdmissible ret.table replyCap frame}) :
    TimedExecution.Procedure (callerStep n κ oracle callerCode callerOracle) Unit
      (Configuration State × Configuration Source) :=
  match hc : selected.val.control with
  | .awaiting caller raw =>
      let valid := selected.property caller raw hc
      simulatorWaitingService oracle positive callerCode callerOracle ret caller selected.val.state
        selected.val.reverseTrace valid.choose
  | _ => TimedExecution.Procedure.ofFixed (callerStep n κ oracle callerCode callerOracle)
      (fun _ => PacketResponseSource.Control.source ret.saved selected.val)
      (fun _ output => PacketResponseSource.Control.source output.1 output.2)
      (fun _ => PMF.pure (ret.saved, selected.val)) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, PMF.pure_map])

theorem simulatorResponse_entry (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (replyCap : Nat)
    (selected : {frame : Configuration Source // SimulatorAdmissible ret.table replyCap frame}) :
    (simulatorResponse oracle positive callerCode callerOracle ret replyCap selected).entry () =
      PacketResponseSource.Control.source ret.saved selected.val := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> try rfl
  case awaiting caller raw =>
    have format := (valid caller raw rfl).choose_spec.1
    have entry : (simulatorResponse oracle positive callerCode callerOracle ret replyCap
        ⟨{ state := state, control := Control.awaiting caller raw, reverseTrace := trace }, valid⟩).entry ()
        = (simulatorWaitingService oracle positive callerCode callerOracle ret caller state trace
            (valid caller raw rfl).choose).entry () := rfl
    have entry' : (simulatorWaitingService oracle positive callerCode callerOracle ret caller state trace
        (valid caller raw rfl).choose).entry ()
        = PacketResponseSource.Control.source ret.saved
            ⟨state, .awaiting caller (compressionPacket (valid caller raw rfl).choose ++ [false]), trace⟩ := rfl
    rw [entry, entry', ← format]

theorem simulatorResponse_exit (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (replyCap : Nat)
    (selected : {frame : Configuration Source // SimulatorAdmissible ret.table replyCap frame})
    (output : Configuration State × Configuration Source) :
    (simulatorResponse oracle positive callerCode callerOracle ret replyCap selected).exit () output =
      PacketResponseSource.Control.source output.1 output.2 := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> rfl

theorem simulatorResponse_budget (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (replyCap : Nat)
    (selected : {frame : Configuration Source // SimulatorAdmissible ret.table replyCap frame}) :
    (simulatorResponse oracle positive callerCode callerOracle ret replyCap selected).budget () ≤ 1 + replyCap := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> try (change 0 ≤ _; omega)
  case awaiting caller raw =>
    have bound := (valid caller raw rfl).choose_spec.2
    change 1 + (SimulatorQueryPacket.steps _ ret.table + (3 * n + 4)) ≤ _
    omega

theorem simulatorSourcePrefix_operational (oracle' : BitOracle State) (callerCode' : Code)
    (callerOracle' : BitOracle Source) (ret : Retained n κ State) :
    TimedExecution.Procedure.Operational (simulatorSourcePrefix oracle' callerCode' callerOracle' ret) := by
  unfold simulatorSourcePrefix SourcePrefix.liftTo
  apply Procedure.operational_liftBoundary

theorem simulatorWaitingService_operational (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) :
    TimedExecution.Procedure.Operational
      (simulatorWaitingService oracle positive callerCode callerOracle ret caller callerState callerTrace query) := by
  apply TimedExecution.Procedure.operational_observe
  apply TimedExecution.Procedure.operational_seq
  · apply TimedExecution.Procedure.operational_ofFixed
  · exact SimulatorQueryService.simulatorService_operational oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace
      query ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
      (compressionPacket query ++ [false])

theorem simulatorResponse_operational (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (replyCap : Nat)
    (selected : {frame : Configuration Source // SimulatorAdmissible ret.table replyCap frame}) :
    TimedExecution.Procedure.Operational
      (simulatorResponse oracle positive callerCode callerOracle ret replyCap selected) := by
  rcases selected with ⟨⟨state, control, trace⟩, valid⟩
  cases control <;> first
  | exact simulatorWaitingService_operational oracle positive callerCode callerOracle ret _ _ _ _
  | apply TimedExecution.Procedure.operational_ofFixed; intro; simp [TimedExecution.eval, PMF.pure_map]

/-- Attach format/length certificates to the request reached by the actual
source, preserving both its physical frame and first-arrival distribution. -/
noncomputable def simulatorCertifiedPrefix (oracle : BitOracle State) (callerCode : Code)
    (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle)
    (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :=
  ((simulatorSourcePrefix oracle callerCode callerOracle ret).reindex
    (fun _ : Unit => selection)).certify (SimulatorAdmissible ret.table replyCap)
      (fun _ frame hs => valid frame hs)

noncomputable def simulatorSourceCombined (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :=
  (simulatorCertifiedPrefix oracle callerCode callerOracle ret selection replyCap valid).seq
    (Procedure.dispatch (simulatorResponse oracle positive callerCode callerOracle ret replyCap))
    (fun _ selected _ => simulatorResponse_entry oracle positive callerCode callerOracle ret replyCap selected)
    (fun _ => 1 + replyCap)
    (fun _ selected _ => simulatorResponse_budget oracle positive callerCode callerOracle ret replyCap selected)

/-- One actual source round, including selection, dispatch, native evaluation
and response loading. No machine state is normalized at the return. -/
noncomputable def simulatorSourceRound (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :=
  (simulatorSourceCombined oracle positive callerCode callerOracle ret selection replyCap valid).observe Prod.snd
    (fun _ output => PacketResponseSource.Control.source output.1 output.2)
    (fun _ output _ => (simulatorResponse_exit oracle positive callerCode callerOracle ret replyCap
      output.1 output.2).symm)

theorem simulatorSourceRound_entry (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :
    (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).entry () =
      PacketResponseSource.Control.source ret.saved selection.start := rfl

theorem simulatorSourceRound_exit (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame)
    (output : Configuration State × Configuration Source) :
    (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).exit () output =
      PacketResponseSource.Control.source output.1 output.2 := rfl

theorem simulatorSourceRound_budget (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :
    (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).budget () =
      selection.budget + (1 + replyCap) := rfl

/-- Erasing proof data recovers exactly the source boundary distribution. -/
theorem simulatorCertifiedPrefix_erase (callerCode : Code) (callerOracle : BitOracle Source)
    (ret : Retained n κ State) (selection : SourcePrefix.Input callerCode callerOracle)
    (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :
    ((simulatorCertifiedPrefix oracle callerCode callerOracle ret selection replyCap valid).semantics ()).map
      Subtype.val =
    TimedExecution.eval (SourcePrefix.step callerCode callerOracle) selection.budget selection.start := by
  exact Procedure.certify_semantics _ _ _ ()

theorem simulatorSourceRound_semantics (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :
    (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).semantics () =
      ((simulatorCertifiedPrefix oracle callerCode callerOracle ret selection replyCap valid).semantics ()).bind
        (fun selected => (simulatorResponse oracle positive callerCode callerOracle ret replyCap selected).semantics ()) := by
  simp only [simulatorSourceRound, simulatorSourceCombined, Procedure.observe, Procedure.seq,
    Procedure.dispatch, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [show (fun x : Configuration State × Configuration Source => x) = id by rfl, PMF.map_id]

theorem simulatorSourceRound_operational (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame) :
    TimedExecution.Procedure.Operational
      (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid) := by
  apply TimedExecution.Procedure.operational_observe
  apply TimedExecution.Procedure.operational_seq
  · apply TimedExecution.Procedure.operational_certify
    apply TimedExecution.Procedure.operational_reindex
    exact simulatorSourcePrefix_operational oracle callerCode callerOracle ret
  · apply TimedExecution.Procedure.operational_dispatch
    intro selected
    exact simulatorResponse_operational oracle positive callerCode callerOracle ret replyCap selected

/-- Resume the unchanged physical controller using the sum of actual
selection and response costs, not the sum of their worst-case bounds. -/
theorem simulatorSourceRound_law (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat) (horizon : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame)
    (enough : selection.budget + (1 + replyCap) ≤ horizon) :
    TimedExecution.eval (callerStep n κ oracle callerCode callerOracle) horizon
      (PacketResponseSource.Control.source ret.saved selection.start) =
    ((simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).costed ()).bind
        (fun result => TimedExecution.eval (callerStep n κ oracle callerCode callerOracle) (horizon - result.2)
          (PacketResponseSource.Control.source result.1.1 result.1.2)) :=
  (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).law () horizon enough

/-- The captured frame's actual native preparation may be deterministic. -/
theorem simulatorSourceRound_semantics_of_pure (oracle : BitOracle State) (positive : 0 < n)
    (callerCode : Code) (callerOracle : BitOracle Source) (ret : Retained n κ State)
    (selection : SourcePrefix.Input callerCode callerOracle) (replyCap : Nat)
    (valid : ∀ frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start).support, SimulatorAdmissible ret.table replyCap frame)
    (caller : Machine.Configuration)
    (callerState : Source) (callerTrace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (selectedPure : TimedExecution.eval (SourcePrefix.step callerCode callerOracle)
      selection.budget selection.start =
      PMF.pure ⟨callerState, .awaiting caller (compressionPacket query ++ [false]), callerTrace⟩) :
    (simulatorSourceRound oracle positive callerCode callerOracle ret selection replyCap valid).semantics () =
    (SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine ret.saved.reverseTrace query
      ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
      (compressionPacket query ++ [false])).semantics () := by
  let D := (simulatorCertifiedPrefix oracle callerCode callerOracle ret selection replyCap valid).semantics ()
  have erase : D.map Subtype.val =
      PMF.pure ⟨callerState, .awaiting caller (compressionPacket query ++ [false]), callerTrace⟩ := by
    rw [simulatorCertifiedPrefix_erase, selectedPure]
  rw [simulatorSourceRound_semantics, ← PMF.bindOnSupport_eq_bind]
  change D.bindOnSupport _ = _
  trans D.bindOnSupport (fun _ _ => (SimulatorQueryService.simulatorService oracle ret.table ret.saved.state ret.machine
    ret.saved.reverseTrace query ret.tableLayout positive callerCode callerOracle caller callerState callerTrace
    (compressionPacket query ++ [false])).semantics ())
  · congr 1
    funext selected hs
    obtain ⟨frame, prop⟩ := selected
    have selectedFrame : frame =
        ⟨callerState, .awaiting caller (compressionPacket query ++ [false]), callerTrace⟩ := by
      have hm : frame ∈ (D.map Subtype.val).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨⟨frame, prop⟩, hs, rfl⟩
      rwa [erase, PMF.mem_support_pure_iff] at hm
    have captured : frame.control = .awaiting caller (compressionPacket query ++ [false]) := by
      rw [selectedFrame]
    rw [simulatorResponse]
    split
    · next caller' raw' hc =>
        have chosen := (prop caller' raw' hc).choose_spec.1
        have hEq : Control.awaiting caller' raw'
            = Control.awaiting caller (compressionPacket query ++ [false]) := hc.symm.trans captured
        have hRaw : raw' = compressionPacket query ++ [false] := by
          injection hEq with _ h2
        have hCaller : caller' = caller := by
          injection hEq with h1 _
        have hList : compressionPacket (prop caller' raw' hc).choose ++ [false]
            = compressionPacket query ++ [false] := chosen.symm.trans hRaw
        have hQ : (prop caller' raw' hc).choose = query :=
          compressionPacket_injective n κ (List.append_left_injective [false] hList)
        have hState : frame.state = callerState := by rw [selectedFrame]
        have hTrace : frame.reverseTrace = callerTrace := by rw [selectedFrame]
        rw [simulatorWaitingService_semantics, hQ, hCaller]
        simp only [hState, hTrace]
    · next hc =>
        exact (hc caller (compressionPacket query ++ [false]) captured).elim
  · rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

end Foundation.Hash.Native.SimulatorQueryRound
