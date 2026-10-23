import Foundation.Constructions.Hash.NativeCompactMACRound
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeRequests
import Foundation.Crypto.Semantics.Oracle.SourcePrefixExactTime
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Physical MAC request rounds parameterized by the actual caller code.
The old retained-frame/table decoder is reused. Capture, server admission,
lookup/fresh generation, return loading and caller resumption remain timed
inside one PacketResponseSource runtime. -/
namespace Foundation.Hash.Native.ConfiguredMACRound
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

open CompactMACRound

noncomputable def step (callerCode : Code) {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source) :
    Control State Source → PMF (Control State Source) :=
  PacketResponseSource.step (CompactMACPacket.step oracle) CompactMACService.beginRound CompactMACPacket.ready callerCode callerOracle

variable (callerCode : Code) {State Source : Type} (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (ret : Retained State) (caller : Machine.Configuration) (callerState : Source)
    (trace : List (List Bool × List Bool)) (message : Message)
    (before after : List (Option Bool)) (active : caller.halted = false)
    (call : callerCode[caller.pc]? = some .call)
    (tape : caller.outputTape = RequestExport.packetTape before after (encodeMessage message))

noncomputable def sourcePrefix : Procedure (step callerCode oracle callerOracle)
    (SourcePrefix.Input callerCode callerOracle) (Configuration Source) :=
  SourcePrefix.liftTo callerCode callerOracle (step callerCode oracle callerOracle) boundary
    (.source ret.saved) (fun _ => rfl) (by
      intro frame nonterminal
      cases hc : frame.control <;>
        simp_all [SourcePrefix.boundary, SourcePrefix.step, step, PacketResponseSource.step])

def captureInput : SourcePrefix.Input callerCode callerOracle where
  start := ⟨callerState, .running caller, trace⟩
  budget := 9
  complete := by
    intro frame supported
    have run := SourcePrefix.capture_run callerCode callerOracle caller callerState trace (encodeMessage message) before after active call tape
    simp only [message_width] at run
    rw [run, PMF.mem_support_pure_iff] at supported
    subst frame
    rfl

noncomputable def capture : Procedure (step callerCode oracle callerOracle) Unit Unit :=
  ((sourcePrefix callerCode oracle callerOracle ret).reindex (fun _ : Unit =>
    captureInput callerCode callerOracle caller callerState trace message before after active call tape)).observe (fun _ => ())
    (fun _ _ => .source ret.saved ⟨callerState, .awaiting caller.advance (encodeMessage message), trace⟩) (by
      intro _ frame supported
      change frame ∈ (TimedExecution.eval (SourcePrefix.step callerCode callerOracle) 9
        ⟨callerState, .running caller, trace⟩).support at supported
      have run := SourcePrefix.capture_run callerCode callerOracle caller callerState trace (encodeMessage message) before after active call tape
      simp only [message_width] at run
      rw [run, PMF.mem_support_pure_iff] at supported
      subst frame
      rfl)

theorem capture_semantics :
    (capture callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics () = PMF.pure () := by
  change (TimedExecution.eval (SourcePrefix.step callerCode callerOracle) 9
    ⟨callerState, .running caller, trace⟩).map (fun _ => ()) = _
  have run := SourcePrefix.capture_run callerCode callerOracle caller callerState trace (encodeMessage message) before after active call tape
  simp only [message_width] at run
  rw [run, PMF.pure_map]

noncomputable def admission : Procedure (step callerCode oracle callerOracle) Unit Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .awaiting caller.advance (encodeMessage message), trace⟩)
    (fun _ _ => .processing caller.advance callerState trace (encodeMessage message)
      (.admitting ret.saved.state ret.machine ret.saved.reverseTrace (encodeMessage message)))
    (fun _ => PMF.pure ()) (fun _ => 1) (by
      intro _
      simp only [TimedExecution.eval, step, PacketResponseSource.step, CompactMACService.beginRound,
        SimulatorQueryService.retainedMachine, ret.hControl, PMF.pure_bind, PMF.pure_map])

noncomputable def waiting :=
  ((admission callerCode oracle callerOracle ret caller callerState trace message).seq
    (CompactMACService.service oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
      callerCode callerOracle caller.advance callerState trace)
    (fun _ _ _ => rfl) (fun _ => CompactMACQuery.steps message ret.table + 49)
    (fun _ _ _ => le_of_eq (CompactMACService.service_budget ..))).observe Prod.snd
      (fun _ output => .source output.1 output.2) (fun _ _ _ => rfl)

noncomputable def raw :=
  ((capture callerCode oracle callerOracle ret caller callerState trace message before after active call tape).seq
    (waiting callerCode oracle callerOracle ret caller callerState trace message)
    (fun _ _ _ => rfl) (fun _ => 1 + (CompactMACQuery.steps message ret.table + 49))
    (fun _ _ _ => Nat.le_refl _)).observe Prod.snd
      (fun _ output => .source output.1 output.2) (fun _ _ _ => rfl)

theorem raw_semantics :
    (raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics () =
    (CompactMACService.service oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
      callerCode callerOracle caller.advance callerState trace).semantics () := by
  simp only [raw, Procedure.observe, Procedure.seq, capture_semantics, waiting, admission,
    TimedExecution.Procedure.ofFixed, PMF.map_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem raw_budget :
    (raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape).budget () =
      CompactMACQuery.steps message ret.table + 59 := by
  change 9 + (1 + (CompactMACQuery.steps message ret.table + 49)) = _
  omega

theorem raw_operational : Procedure.Operational
    (raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape) := by
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

theorem raw_returned (output : Configuration State × Configuration Source)
    (supported : output ∈ ((raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).support) :
    Returned ret caller callerState trace message output := by
  rw [raw_semantics] at supported
  exact CompactMACService.service_retained oracle ret.saved.state ret.machine ret.saved.reverseTrace message ret.table ret.tableLayout
    callerCode callerOracle caller.advance callerState trace output supported

noncomputable def certified : Procedure (step callerCode oracle callerOracle) Unit
    {output // Returned ret caller callerState trace message output} :=
  (raw callerCode oracle callerOracle ret caller callerState trace message before after active call tape).certify
    (Returned ret caller callerState trace message)
    (fun _ output supported => raw_returned callerCode oracle callerOracle ret caller callerState trace message before after active call tape output supported)

noncomputable def query : Procedure (step callerCode oracle callerOracle) Unit (Retained State × Tag) :=
  (certified callerCode oracle callerOracle ret caller callerState trace message before after active call tape).observe
    (answer ret caller callerState trace message)
    (fun _ output => .source output.1.saved
      (NativeCallback.resumed caller.advance callerState trace (encodeMessage message) (encodeTag output.2)))
    (fun _ output _ => by rw [(answer_exit ret caller callerState trace message output).1,
      (answer_exit ret caller callerState trace message output).2]; rfl)

theorem query_budget :
    (query callerCode oracle callerOracle ret caller callerState trace message before after active call tape).budget () =
      CompactMACQuery.steps message ret.table + 59 := raw_budget ..

theorem query_bound (entries : Nat) (size : ret.table.length ≤ entries) :
    (query callerCode oracle callerOracle ret caller callerState trace message before after active call tape).budget () ≤
      146 * entries + 254 := by
  rw [query_budget]
  have bound := CompactMACQuery.steps_budget message ret.table entries size
  omega

theorem query_operational : Procedure.Operational
    (query callerCode oracle callerOracle ret caller callerState trace message before after active call tape) := by
  apply Procedure.operational_observe
  apply Procedure.operational_certify
  exact raw_operational callerCode oracle callerOracle ret caller callerState trace message before after active call tape

/-- Each physical query increases the represented table by at most one. -/
theorem query_growth (output : Retained State × Tag)
    (supported : output ∈ ((query callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 := by
  change output ∈ (((certified callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics ()).map
    (answer ret caller callerState trace message)).support at supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨result, _, rfl⟩ := supported
  change (if (ret.table.lookup (Backend.key message)).isSome then ret.table
    else (Backend.key message, result.property.choose) :: ret.table).length ≤ ret.table.length + 1
  split <;> simp

/-- Accepted native segments execute in the same outer caller/server
runtime, preserving its full retained private frame and both transcripts. -/
theorem native_run (count : Nat) (start finish : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some finish) :
    TimedExecution.eval (step callerCode oracle callerOracle) count
      (.source ret.saved ⟨callerState, .running start, trace⟩) =
      PMF.pure (.source ret.saved ⟨callerState, .running finish, trace⟩) := by
  induction count generalizing start with
  | zero => cases checked; rfl
  | succ count ih =>
      cases first : NativeDeterministic.next? callerCode start with
      | none => simp [NativeDeterministic.run, first] at checked
      | some middle =>
          have rest : NativeDeterministic.run callerCode count middle = some finish := by
            simpa only [NativeDeterministic.run, first, Option.bind_some] using checked
          have one : step callerCode oracle callerOracle (.source ret.saved ⟨callerState, .running start, trace⟩) =
              PMF.pure (.source ret.saved ⟨callerState, .running middle, trace⟩) := by
            change (Reification.timedStep callerCode callerOracle ⟨callerState, .running start, trace⟩).map (PacketResponseSource.Control.source ret.saved) = _
            rw [NativeDeterministic.next_sound callerCode callerOracle callerState trace start middle first, PMF.pure_map]
          rw [TimedExecution.eval, one, PMF.pure_bind]
          exact ih middle rest

noncomputable def nativeSegment (count : Nat) (start finish : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some finish) : Procedure (step callerCode oracle callerOracle) Unit Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => .source ret.saved ⟨callerState, .running start, trace⟩)
    (fun _ _ => .source ret.saved ⟨callerState, .running finish, trace⟩)
    (fun _ => PMF.pure ()) (fun _ => count) (fun _ => by
      simpa only [PMF.pure_map] using native_run callerCode oracle callerOracle ret callerState trace count start finish checked)

/-- A native setup segment followed by its actual physical query. -/
noncomputable def prefixed (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some caller) :
    Procedure (step callerCode oracle callerOracle) Unit (Retained State × Tag) :=
  ((nativeSegment callerCode oracle callerOracle ret callerState trace count start caller checked).seq
    (query callerCode oracle callerOracle ret caller callerState trace message before after active call tape)
    (fun _ _ _ => rfl) (fun _ => CompactMACQuery.steps message ret.table + 59)
    (fun _ _ _ => le_of_eq (query_budget ..))).observe Prod.snd
      (fun _ output => .source output.1.saved
        (NativeCallback.resumed caller.advance callerState trace (encodeMessage message) (encodeTag output.2)))
      (fun _ _ _ => rfl)

theorem prefixed_semantics (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some caller) :
    (prefixed callerCode oracle callerOracle ret caller callerState trace message before after active call tape count start checked).semantics () =
      (query callerCode oracle callerOracle ret caller callerState trace message before after active call tape).semantics () := by
  simp only [prefixed, nativeSegment, TimedExecution.Procedure.ofFixed, Procedure.seq, Procedure.observe,
    PMF.pure_bind, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem prefixed_growth (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some caller)
    (output : Retained State × Tag)
    (supported : output ∈ ((prefixed callerCode oracle callerOracle ret caller callerState trace message before after active call tape count start checked).semantics ()).support) :
    output.1.table.length ≤ ret.table.length + 1 := by
  rw [prefixed_semantics] at supported
  exact query_growth callerCode oracle callerOracle ret caller callerState trace message before after active call tape output supported

theorem prefixed_bound (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some caller) :
    (prefixed callerCode oracle callerOracle ret caller callerState trace message before after active call tape count start checked).budget () ≤
      count + 146 * ret.table.length + 254 := by
  change count + (CompactMACQuery.steps message ret.table + 59) ≤ _
  have bound := CompactMACQuery.steps_budget message ret.table ret.table.length (Nat.le_refl _)
  omega

theorem prefixed_operational (count : Nat) (start : Machine.Configuration)
    (checked : NativeDeterministic.run callerCode count start = some caller) : Procedure.Operational
    (prefixed callerCode oracle callerOracle ret caller callerState trace message before after active call tape count start checked) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_ofFixed
  · exact query_operational callerCode oracle callerOracle ret caller callerState trace message before after active call tape

end Foundation.Hash.Native.ConfiguredMACRound
