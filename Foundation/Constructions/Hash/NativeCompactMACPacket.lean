import Foundation.Constructions.Hash.NativeCompactMACQuery
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! A continuing compact-request component with real response export.
The first native halt is charged at its actual arrival time; the existing
cell exporter then takes 21 transitions for the eight-bit response. The
private native frame is retained and never rebuilt from a logical table.
-/
namespace Foundation.Hash.Native.CompactMACPacket
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type) where
  | admitting (state : State) (machine : Machine.Configuration)
      (trace : List (List Bool × List Bool)) (request : List Bool)
  | running (component : NativePacketComponent.Control State)

noncomputable def step {State : Type} (oracle : BitOracle State) : Control State → PMF (Control State)
  | .admitting state machine trace request => PMF.pure (.running (.computing
      ⟨state, .loading (machine.resumeAt CompactMACQuery.source.length) request {}, trace⟩))
  | .running component => (NativePacketComponent.step CompactMACQuery.code oracle component).map .running

def embed {State : Type} : SimulatorQueryLoading.Control State → Control State
  | .admitting state machine trace request => .admitting state machine trace request
  | .executing frame => .running (.computing frame)

def nativeBoundary {State : Type} : Control State → Bool
  | .admitting .. => false
  | .running component => NativePacketComponent.boundary component

def ready {State : Type} : Control State → Option (Configuration State × List Bool)
  | .admitting .. => none
  | .running component => NativePacketComponent.ready component

def Exportable {State : Type} (control : SimulatorQueryLoading.Control State) : Prop :=
  ∃ (state : State) (trace : List (List Bool × List Bool)) (actual : Machine.Configuration)
      (before : List (Option Bool)) (value : Bits 8),
    control = .executing (NativeCode.frame state trace actual) ∧ actual.halted = true ∧
      before.getD 0 none = none ∧
      actual.outputTape.Equivalent (FixedWidthCopy.frontier before (value.toList.map some ++ [none])) ∧
      SimulatorDispatchQueryLoading.headBits actual.outputTape = value.toList

/-- Logical description of the exporter exit, not a runtime encoder. -/
def exported {State : Type} : SimulatorQueryLoading.Control State → Control State
  | .admitting state machine trace request => .admitting state machine trace request
  | .executing frame => .running (.exporting frame (.returned (match frame.control with
      | .running machine => SimulatorDispatchQueryLoading.headBits machine.outputTape
      | _ => [])))

theorem native_absorbing {State : Type} (oracle : BitOracle State) (control : SimulatorQueryLoading.Control State)
    (halted : SimulatorQueryLoading.boundary control = true) : CompactMACQuery.step oracle control = PMF.pure control := by
  cases control with
  | admitting => contradiction
  | executing frame =>
      change Reification.terminal frame.control = true at halted
      simp [CompactMACQuery.step, Reification.timedStep, halted, PMF.pure_map]

theorem boundary_embed {State : Type} (control : SimulatorQueryLoading.Control State) :
    nativeBoundary (embed control) = SimulatorQueryLoading.boundary control := by cases control <;> rfl

theorem embed_step {State : Type} (oracle : BitOracle State) (control : SimulatorQueryLoading.Control State)
    (active : SimulatorQueryLoading.boundary control = false) :
    step oracle (embed control) = (CompactMACQuery.step oracle control).map embed := by
  cases control with
  | admitting => simp [step, embed, CompactMACQuery.step, PMF.pure_map]
  | executing frame =>
      change Reification.terminal frame.control = false at active
      simp [step, embed, CompactMACQuery.step, NativePacketComponent.step, active, PMF.map_comp, Function.comp_def]

theorem export_run {State : Type} (oracle : BitOracle State)
    (input : {control : SimulatorQueryLoading.Control State // Exportable control}) :
    TimedExecution.eval (step oracle) 21 (embed input.val) = PMF.pure (exported input.val) := by
  obtain ⟨state, trace, actual, before, value, same, halted, blank, output, bits⟩ := input.property
  rw [same]
  have liftRun (fuel : Nat) (component : NativePacketComponent.Control State) :
      TimedExecution.eval (step oracle) fuel (.running component) =
        (TimedExecution.eval (NativePacketComponent.step CompactMACQuery.code oracle) fuel component).map .running := by
    induction fuel generalizing component with
    | zero => simp [TimedExecution.eval, PMF.pure_map]
    | succ fuel ih => simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]
  rw [embed, liftRun]
  simpa only [Bits.length_toList, exported, NativeCode.frame, bits, PMF.pure_map] using
    congrArg (PMF.map Control.running)
      (NativePacketComponent.export_prefix_run CompactMACQuery.code oracle state actual trace value.toList before [] blank halted output)

theorem exported_ready {State : Type} (input : {control : SimulatorQueryLoading.Control State // Exportable control}) :
    (ready (exported input.val)).isSome = true := by
  obtain ⟨state, trace, actual, before, value, same, halted, blank, output, bits⟩ := input.property
  rw [same]
  rfl

variable {State : Type} (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (message : Message) (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))

noncomputable def core : Procedure (CompactMACQuery.step oracle) Unit (SimulatorQueryLoading.Control State) :=
  Procedure.ofFixed _ (fun _ => .admitting state machine trace (encodeMessage message))
    (fun _ output => output)
    (fun _ => TimedExecution.eval (CompactMACQuery.step oracle) (CompactMACQuery.steps message table)
      (.admitting state machine trace (encodeMessage message)))
    (fun _ => CompactMACQuery.steps message table) (fun _ => (PMF.map_id _).symm)

include layout in
theorem core_terminal (output : SimulatorQueryLoading.Control State)
    (supported : output ∈ ((core oracle state machine trace message table).semantics ()).support) :
    SimulatorQueryLoading.boundary output = true := by
  obtain ⟨actual, same, halted⟩ := CompactMACQuery.native_halts oracle state machine trace message table layout output supported
  rw [same]
  exact halted

noncomputable def lifted : Procedure (step oracle) Unit (SimulatorQueryLoading.Control State) :=
  (core oracle state machine trace message table).liftBoundary SimulatorQueryLoading.boundary
    (fun _ output supported => core_terminal oracle state machine trace message table layout output supported)
    (native_absorbing oracle) (fun _ output => output) (fun _ _ => rfl)
    (step oracle) nativeBoundary embed boundary_embed (embed_step oracle)

theorem lifted_exportable (output : SimulatorQueryLoading.Control State)
    (supported : output ∈ ((lifted oracle state machine trace message table layout).semantics ()).support) : Exportable output := by
  obtain ⟨value, before, actual, same, halted, _, blank, cells, bits⟩ :=
    CompactMACQuery.native_retained oracle state machine trace message table layout output supported
  exact ⟨state, trace, actual, before, value, same, halted, blank, cells, bits⟩

noncomputable def certified : Procedure (step oracle) Unit
    {control : SimulatorQueryLoading.Control State // Exportable control} := (lifted oracle state machine trace message table layout).certify Exportable
  (fun _ output supported => lifted_exportable oracle state machine trace message table layout output supported)

noncomputable def exporter : Procedure (step oracle)
    {control : SimulatorQueryLoading.Control State // Exportable control} Unit :=
  Procedure.ofFixed _ (fun input => embed input.val) (fun input _ => exported input.val)
    (fun _ => PMF.pure ()) (fun _ => 21) (fun input => by simpa only [PMF.pure_map] using export_run oracle input)

noncomputable def whole : Procedure (step oracle) Unit (Control State) :=
  ((certified oracle state machine trace message table layout).seq (exporter oracle)
    (fun _ _ _ => rfl) (fun _ => 21) (fun _ _ _ => Nat.le_refl _)).observe
      (fun output => exported output.1.val) (fun _ output => output) (fun _ _ _ => rfl)

theorem whole_budget : (whole oracle state machine trace message table layout).budget () =
    CompactMACQuery.steps message table + 21 := rfl

theorem whole_operational : Procedure.Operational (whole oracle state machine trace message table layout) := by
  apply Procedure.operational_observe
  apply Procedure.operational_seq
  · apply Procedure.operational_certify
    exact Procedure.operational_liftBoundary _ _ _ _ _ _ _ _ _ _ _
  · apply Procedure.operational_ofFixed

/-- The component changes neither the native result distribution nor its
retained physical frame; it only executes the physical response scan. -/
theorem whole_semantics :
    (whole oracle state machine trace message table layout).semantics () =
      ((core oracle state machine trace message table).semantics ()).map exported := by
  simp only [whole, Procedure.observe, Procedure.seq, exporter, TimedExecution.Procedure.ofFixed,
    PMF.map_bind, PMF.pure_map]
  change ((certified oracle state machine trace message table layout).semantics ()).map
    (exported ∘ Subtype.val) = _
  rw [← PMF.map_comp]
  unfold certified
  rw [Procedure.certify_semantics]
  rfl

theorem whole_ready (output : Control State)
    (supported : output ∈ ((whole oracle state machine trace message table layout).semantics ()).support) :
    (ready output).isSome = true := by
  rw [whole_semantics, PMF.mem_support_map_iff] at supported
  obtain ⟨native, hn, same⟩ := supported
  subst output
  exact exported_ready ⟨native, lifted_exportable oracle state machine trace message table layout native hn⟩

/-- The physically exported packet and the updated private tape use the
same response value. The original server state and trace are retained. -/
theorem whole_retained (output : Control State)
    (supported : output ∈ ((whole oracle state machine trace message table layout).semantics ()).support) :
    ∃ (value : Bits 8) (actual : Machine.Configuration),
      output = .running (.exporting (NativeCode.frame state trace actual) (.returned value.toList)) ∧
      actual.halted = true ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup (Backend.key message)).isSome then table else (Backend.key message, value) :: table))) := by
  rw [whole_semantics, PMF.mem_support_map_iff] at supported
  obtain ⟨native, hn, same⟩ := supported
  obtain ⟨value, before, actual, eq, halted, input, blank, cells, bits⟩ :=
    CompactMACQuery.native_retained oracle state machine trace message table layout native hn
  subst native
  exact ⟨value, actual, by simpa only [exported, NativeCode.frame, bits] using same.symm, halted, input⟩

theorem ready_absorbing (output : Control State) (returned : (ready output).isSome = true) :
    step oracle output = PMF.pure output := by
  cases output with
  | admitting => simp [ready] at returned
  | running component =>
      change (NativePacketComponent.ready component).isSome = true at returned
      simp only [step, NativePacketComponent.ready_absorbing CompactMACQuery.code oracle component returned, PMF.pure_map]

include layout in
/-- Actual execution at the stated horizon. Earlier native halts continue
immediately into export; no absorbing native padding is charged as work. -/
theorem whole_run (horizon : Nat) (enough : CompactMACQuery.steps message table + 21 ≤ horizon) :
    TimedExecution.eval (step oracle) horizon (.admitting state machine trace (encodeMessage message)) =
      ((core oracle state machine trace message table).semantics ()).map exported := by
  have run := (whole oracle state machine trace message table layout).final_run ()
    (fun output hs => ready_absorbing oracle output (whole_ready oracle state machine trace message table layout output hs))
    horizon enough
  rw [whole_semantics] at run
  change TimedExecution.eval (step oracle) horizon (.admitting state machine trace (encodeMessage message)) =
    (((core oracle state machine trace message table).semantics ()).map exported).map id at run
  simpa only [PMF.map_id] using run

theorem whole_steps_budget (entries : Nat) (size : table.length ≤ entries) :
    (whole oracle state machine trace message table layout).budget () ≤ 146 * entries + 216 := by
  rw [whole_budget]
  have bound := CompactMACQuery.steps_budget message table entries size
  omega

/-- Each reported outcome is reached at its actual reported time, bounded
by the table-size cap, and has an exported eight-bit response. -/
theorem whole_costed (result : Control State × Nat)
    (supported : result ∈ ((whole oracle state machine trace message table layout).costed ()).support)
    (entries : Nat) (size : table.length ≤ entries) :
    result.1 ∈ (TimedExecution.eval (step oracle) result.2
      (.admitting state machine trace (encodeMessage message))).support ∧
    result.2 ≤ 146 * entries + 216 ∧ (ready result.1).isSome = true := by
  exact ⟨whole_operational oracle state machine trace message table layout () result supported,
    ((whole oracle state machine trace message table layout).bounded () result supported).trans
      (whole_steps_budget oracle state machine trace message table layout entries size),
    whole_ready oracle state machine trace message table layout result.1
      ((whole oracle state machine trace message table layout).result_support () result supported)⟩

end Foundation.Hash.Native.CompactMACPacket
