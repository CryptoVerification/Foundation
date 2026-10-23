import Foundation.Constructions.Hash.NativeCompactMACService
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeRequests
import Foundation.Crypto.Semantics.Oracle.SourcePrefixExactTime
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Capture a real MAC caller request, service it from the retained native
cache, and return a certified table and tag. The same fixed outer transition
system executes capture, admission, server work and caller resumption. -/
namespace Foundation.Hash.Native.CompactMACRound
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

abbrev Retained (State : Type) := SimulatorQueryRound.Retained 8 0 State
abbrev Control (State Source : Type) :=
  PacketResponseSource.Control (CompactMACPacket.Control State) Source (Configuration State)

noncomputable def step {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source) :
    Control State Source → PMF (Control State Source) :=
  PacketResponseSource.step (CompactMACPacket.step oracle) CompactMACService.beginRound CompactMACPacket.ready Native.code callerOracle

def boundary {State Source : Type} : Control State Source → Bool
  | .source _ frame => SourcePrefix.boundary frame
  | _ => true

variable {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (caller : Machine.Configuration) (callerState : Source)
    (trace : List (List Bool × List Bool)) (message : Message)
    (before after : List (Option Bool)) (active : caller.halted = false)
    (call : Native.code[caller.pc]? = some .call)
    (tape : caller.outputTape = RequestExport.packetTape before after (encodeMessage message))

noncomputable def sourcePrefix : Procedure (step oracle callerOracle)
    (SourcePrefix.Input Native.code callerOracle) (Configuration Source) :=
  SourcePrefix.liftTo Native.code callerOracle (step oracle callerOracle) boundary
    (.source ret.saved) (fun _ => rfl) (by
      intro frame nonterminal
      cases hc : frame.control <;>
        simp_all [SourcePrefix.boundary, SourcePrefix.step, step, PacketResponseSource.step])

def captureInput : SourcePrefix.Input Native.code callerOracle where
  start := ⟨callerState, .running caller, trace⟩
  budget := 9
  complete := by
    intro frame supported
    have run := SourcePrefix.capture_run Native.code callerOracle caller callerState trace (encodeMessage message) before after active call tape
    simp only [message_width] at run
    rw [run, PMF.mem_support_pure_iff] at supported
    subst frame
    rfl

noncomputable def capture : Procedure (step oracle callerOracle) Unit Unit :=
  ((sourcePrefix oracle callerOracle ret).reindex (fun _ : Unit =>
    captureInput callerOracle caller callerState trace message before after active call tape)).observe (fun _ => ())
    (fun _ _ => .source ret.saved ⟨callerState, .awaiting caller.advance (encodeMessage message), trace⟩) (by
      intro _ frame supported
      change frame ∈ (TimedExecution.eval (SourcePrefix.step Native.code callerOracle) 9
        ⟨callerState, .running caller, trace⟩).support at supported
      have run := SourcePrefix.capture_run Native.code callerOracle caller callerState trace (encodeMessage message) before after active call tape
      simp only [message_width] at run
      rw [run, PMF.mem_support_pure_iff] at supported
      subst frame
      rfl)

theorem capture_semantics :
    (capture oracle callerOracle ret caller callerState trace message before after active call tape).semantics () = PMF.pure () := by
  change (TimedExecution.eval (SourcePrefix.step Native.code callerOracle) 9
    ⟨callerState, .running caller, trace⟩).map (fun _ => ()) = _
  have run := SourcePrefix.capture_run Native.code callerOracle caller callerState trace (encodeMessage message) before after active call tape
  simp only [message_width] at run
  rw [run, PMF.pure_map]

noncomputable def admission : Procedure (step oracle callerOracle) Unit Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .awaiting caller.advance (encodeMessage message), trace⟩)
    (fun _ _ => .processing caller.advance callerState trace (encodeMessage message)
      (.admitting ret.saved.state ret.machine ret.saved.reverseTrace (encodeMessage message)))
    (fun _ => PMF.pure ()) (fun _ => 1) (by
      intro _
      simp only [TimedExecution.eval, step, PacketResponseSource.step, CompactMACService.beginRound,
        SimulatorQueryService.retainedMachine, ret.hControl, PMF.pure_bind, PMF.pure_map])

noncomputable def waiting :=
  ((admission oracle callerOracle ret caller callerState trace message).seq
    (CompactMACService.service oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
      Native.code callerOracle caller.advance callerState trace)
    (fun _ _ _ => rfl) (fun _ => CompactMACQuery.steps message ret.table + 49)
    (fun _ _ _ => le_of_eq (CompactMACService.service_budget ..))).observe Prod.snd
      (fun _ output => .source output.1 output.2) (fun _ _ _ => rfl)

noncomputable def raw :=
  ((capture oracle callerOracle ret caller callerState trace message before after active call tape).seq
    (waiting oracle callerOracle ret caller callerState trace message)
    (fun _ _ _ => rfl) (fun _ => 1 + (CompactMACQuery.steps message ret.table + 49))
    (fun _ _ _ => Nat.le_refl _)).observe Prod.snd
      (fun _ output => .source output.1 output.2) (fun _ _ _ => rfl)

theorem raw_semantics :
    (raw oracle callerOracle ret caller callerState trace message before after active call tape).semantics () =
    (CompactMACService.service oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
      Native.code callerOracle caller.advance callerState trace).semantics () := by
  simp only [raw, Procedure.observe, Procedure.seq, capture_semantics, waiting, admission,
    TimedExecution.Procedure.ofFixed, PMF.map_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem raw_budget :
    (raw oracle callerOracle ret caller callerState trace message before after active call tape).budget () =
      CompactMACQuery.steps message ret.table + 59 := by
  change 9 + (1 + (CompactMACQuery.steps message ret.table + 49)) = _
  omega

theorem raw_operational : Procedure.Operational
    (raw oracle callerOracle ret caller callerState trace message before after active call tape) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · unfold capture
    apply Procedure.operational_observe
    apply Procedure.operational_reindex
    unfold sourcePrefix SourcePrefix.liftTo
    apply Procedure.operational_liftBoundary
  · unfold waiting
    apply Procedure.operational_observe
    apply Procedure.operational_seq
    · apply Procedure.operational_ofFixed
    · apply CompactMACService.service_operational

/-- Evidence for a returned response, including its actual physical table. -/
def Returned (output : Configuration State × Configuration Source) : Prop :=
  ∃ (value : Bits 8) (actual : Machine.Configuration),
    output.1 = NativeCode.frame ret.saved.state ret.saved.reverseTrace actual ∧
    actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
      (if (ret.table.lookup (Backend.key message)).isSome then ret.table else (Backend.key message, value) :: ret.table))) ∧
    output.2 = NativeCallback.resumed caller.advance callerState trace (encodeMessage message) value.toList

theorem raw_returned (output : Configuration State × Configuration Source)
    (supported : output ∈ ((raw oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).support) :
    Returned ret caller callerState trace message output := by
  rw [raw_semantics] at supported
  exact CompactMACService.service_retained oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
    Native.code callerOracle caller.advance callerState trace output supported

noncomputable def certified : Procedure (step oracle callerOracle) Unit
    {output // Returned ret caller callerState trace message output} :=
  (raw oracle callerOracle ret caller callerState trace message before after active call tape).certify
    (Returned ret caller callerState trace message)
    (fun _ output supported => raw_returned oracle callerOracle ret caller callerState trace message before after active call tape output supported)

/-- A logical certificate reads the table already stored in the returned
machine. It does not rebuild the machine or execute a host-side lookup. -/
noncomputable def answer (output : {output // Returned ret caller callerState trace message output}) : Retained State × Tag := by
  let value := output.property.choose
  let actual := output.property.choose_spec.choose
  have spec := output.property.choose_spec.choose_spec
  exact ({
    table := if (ret.table.lookup (Backend.key message)).isSome then ret.table else (Backend.key message, value) :: ret.table
    saved := output.val.1
    machine := actual
    hControl := by rw [spec.1]; rfl
    tableLayout := spec.2.1 }, decodeTag value.toList)

theorem encode_decode (value : Bits 8) : encodeTag (decodeTag value.toList) = value.toList := by
  rw [← Backend.tagBits_list, Backend.tagBits_decode]

theorem answer_exit (output : {output // Returned ret caller callerState trace message output}) :
    (answer ret caller callerState trace message output).1.saved = output.val.1 ∧
    NativeCallback.resumed caller.advance callerState trace (encodeMessage message)
      (encodeTag (answer ret caller callerState trace message output).2) = output.val.2 := by
  constructor
  · rfl
  · change NativeCallback.resumed caller.advance callerState trace (encodeMessage message)
      (encodeTag (decodeTag output.property.choose.toList)) = output.val.2
    rw [encode_decode]
    exact output.property.choose_spec.choose_spec.2.2.symm

noncomputable def query : Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  (certified oracle callerOracle ret caller callerState trace message before after active call tape).observe
    (answer ret caller callerState trace message)
    (fun _ output => .source output.1.saved
      (NativeCallback.resumed caller.advance callerState trace (encodeMessage message) (encodeTag output.2)))
    (fun _ output _ => by rw [(answer_exit ret caller callerState trace message output).1,
      (answer_exit ret caller callerState trace message output).2]; rfl)

theorem query_budget :
    (query oracle callerOracle ret caller callerState trace message before after active call tape).budget () =
      CompactMACQuery.steps message ret.table + 59 := raw_budget ..

theorem query_bound (entries : Nat) (size : ret.table.length ≤ entries) :
    (query oracle callerOracle ret caller callerState trace message before after active call tape).budget () ≤
      146 * entries + 254 := by
  rw [query_budget]
  have bound := CompactMACQuery.steps_budget message ret.table entries size
  omega

theorem query_operational : Procedure.Operational
    (query oracle callerOracle ret caller callerState trace message before after active call tape) := by
  apply Procedure.operational_observe
  apply Procedure.operational_certify
  exact raw_operational oracle callerOracle ret caller callerState trace message before after active call tape

/-- Each physical query increases the represented table by at most one. -/
theorem query_growth (output : Retained State × Tag)
    (supported : output ∈ ((query oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 := by
  change output ∈ (((certified oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
    (answer ret caller callerState trace message)).support at supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨result, _, rfl⟩ := supported
  change (if (ret.table.lookup (Backend.key message)).isSome then ret.table
    else (Backend.key message, result.property.choose) :: ret.table).length ≤ ret.table.length + 1
  split <;> simp

/-- Accepted native segments execute in the same outer caller/server
runtime, preserving its full retained private frame and both transcripts. -/
theorem native_run (count : Nat) (start finish : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some finish) :
    TimedExecution.eval (step oracle callerOracle) count
      (.source ret.saved ⟨callerState, .running start, trace⟩) =
      PMF.pure (.source ret.saved ⟨callerState, .running finish, trace⟩) := by
  induction count generalizing start with
  | zero => cases checked; rfl
  | succ count ih =>
      cases first : NativeDeterministic.next? Native.code start with
      | none => simp [NativeDeterministic.run, first] at checked
      | some middle =>
          have rest : NativeDeterministic.run Native.code count middle = some finish := by
            simpa only [NativeDeterministic.run, first, Option.bind_some] using checked
          have one : step oracle callerOracle (.source ret.saved ⟨callerState, .running start, trace⟩) =
              PMF.pure (.source ret.saved ⟨callerState, .running middle, trace⟩) := by
            change (Reification.timedStep Native.code callerOracle ⟨callerState, .running start, trace⟩).map (PacketResponseSource.Control.source ret.saved) = _
            rw [NativeDeterministic.next_sound Native.code callerOracle callerState trace start middle first, PMF.pure_map]
          rw [TimedExecution.eval, one, PMF.pure_bind]
          exact ih middle rest

noncomputable def nativeSegment (count : Nat) (start finish : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some finish) : Procedure (step oracle callerOracle) Unit Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .running start, trace⟩)
    (fun _ _ => .source ret.saved ⟨callerState, .running finish, trace⟩)
    (fun _ => PMF.pure ()) (fun _ => count) (fun _ => by
      simpa only [PMF.pure_map] using native_run oracle callerOracle ret callerState trace count start finish checked)

/-- A native setup segment followed by its actual physical query. -/
noncomputable def prefixed (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some caller) :
    Procedure (step oracle callerOracle) Unit (Retained State × Tag) :=
  ((nativeSegment oracle callerOracle ret callerState trace count start caller checked).seq
    (query oracle callerOracle ret caller callerState trace message before after active call tape)
    (fun _ _ _ => rfl) (fun _ => CompactMACQuery.steps message ret.table + 59)
    (fun _ _ _ => le_of_eq (query_budget ..))).observe Prod.snd
      (fun _ output => .source output.1.saved
        (NativeCallback.resumed caller.advance callerState trace (encodeMessage message) (encodeTag output.2)))
      (fun _ _ _ => rfl)

theorem prefixed_semantics (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some caller) :
    (prefixed oracle callerOracle ret caller callerState trace message before after active call tape count start checked).semantics () =
      (query oracle callerOracle ret caller callerState trace message before after active call tape).semantics () := by
  simp only [prefixed, nativeSegment, TimedExecution.Procedure.ofFixed, Procedure.seq, Procedure.observe,
    PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem prefixed_growth (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some caller)
    (output : Retained State × Tag)
    (supported : output ∈ ((prefixed oracle callerOracle ret caller callerState trace message before after active call tape count start checked).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 := by
  rw [prefixed_semantics] at supported
  exact query_growth oracle callerOracle ret caller callerState trace message before after active call tape output supported

theorem prefixed_bound (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some caller) :
    (prefixed oracle callerOracle ret caller callerState trace message before after active call tape count start checked).budget () ≤
      count + 146 * ret.table.length + 254 := by
  change count + (CompactMACQuery.steps message ret.table + 59) ≤ _
  have bound := CompactMACQuery.steps_budget message ret.table ret.table.length (Nat.le_refl _)
  omega

theorem prefixed_operational (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run Native.code count start = some caller) : Procedure.Operational
    (prefixed oracle callerOracle ret caller callerState trace message before after active call tape count start checked) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_ofFixed
  · exact query_operational oracle callerOracle ret caller callerState trace message before after active call tape

end Foundation.Hash.Native.CompactMACRound
