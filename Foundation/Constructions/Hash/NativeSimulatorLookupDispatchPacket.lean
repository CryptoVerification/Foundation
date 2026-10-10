import Foundation.Constructions.Hash.NativeSimulatorLookupDispatch

/-! Actual packet export from the common cache-or-local-uniform code image.
The retained native frame and the returned packet share the same sampled
value. This still does not implement terminal recognition or repeat calls. -/
namespace Foundation.Hash.Native.SimulatorLookupDispatch
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Joint specification, not an additional runtime sampler or encoder. -/
noncomputable def returned {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) : PMF (Configuration State × List Bool) :=
  match table.lookup query with
  | some value => PMF.pure (SimulatorLookupRestoredHit.finish state trace query table beforeOutput value, value.toList)
  | none => (uniform (Bits n)).map (fun value =>
      (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (CodeRelocation.frame (hitBody n).length
          (SimulatorFreshAfterLookupResponse.finish state trace query table beforeOutput value)), value.toList))

theorem returned_fst {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (returned state trace query table beforeOutput).map Prod.fst = result state trace query table beforeOutput true := by
  cases lookup : table.lookup query <;> simp only [returned, result, lookup, PMF.pure_map, PMF.map_comp]
  rfl

def exportControl {State : Type*} (ready : Bool) (output : Configuration State × List Bool) : NativePacketComponent.Control State :=
  .exporting output.1 (if ready then .returned output.2 else .reversing [] output.2)

theorem export_stage {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (ready : Bool) :
    (returned state trace query table beforeOutput).bind
      (fun output => TimedExecution.eval (NativePacketComponent.step (code n κ) oracle)
        (2 * n + 4 + ready.toNat) (.computing output.1)) =
      (returned state trace query table beforeOutput).map (exportControl ready) := by
  have freshBefore (value : Bits n) := SimulatorFreshAfterLookupResponse.export_before_ready_with_code
    (code n κ) ((SimulatorLookup.lookupCode n κ).length + (hitBody n).length)
    oracle state trace query table beforeOutput value
  have freshAfter (value : Bits n) := SimulatorFreshAfterLookupResponse.export_run_with_code
    (code n κ) ((SimulatorLookup.lookupCode n κ).length + (hitBody n).length)
    oracle state trace query table beforeOutput value
  cases ready <;> cases lookup : table.lookup query with
  | some value =>
      simp only [returned, lookup, PMF.pure_bind, PMF.pure_map, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
      first
      | simpa only [Bool.toNat_false, Nat.add_zero, exportControl, ↓reduceIte] using
          SimulatorLookupRestoredHit.export_stage_with_code (code n κ) oracle state trace query table beforeOutput value false
      | simpa only [Bool.toNat_true, show 2 * n + 4 + 1 = 2 * n + 5 by omega, exportControl, ↓reduceIte] using
          SimulatorLookupRestoredHit.export_stage_with_code (code n κ) oracle state trace query table beforeOutput value true
  | none =>
      simp only [returned, lookup, PMF.bind_map, PMF.map_comp, Function.comp_def,
        Bool.toNat_false, Bool.toNat_true, Nat.add_zero, CodeRelocation.frame_add]
      first
      | simp_rw [freshBefore]
        rfl
      | simp_rw [show 2 * n + 4 + 1 = 2 * n + 5 by omega, freshAfter]
        rfl

theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary (steps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (result state trace query table beforeOutput true).map (fun frame => (.computing frame, steps query table)) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]),
    first_joint oracle state trace query table beforeOutput positive, PMF.map_comp]
  rfl

def packetSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := steps query table + (2 * n + 5)

theorem packet_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) (ready : Bool) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle)
      (steps query table + (2 * n + 4 + ready.toNat))
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (returned state trace query table beforeOutput).map (exportControl ready) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by omega), component_first_joint oracle state trace query table beforeOutput positive, PMF.bind_map]
  simp only [Function.comp_def, Nat.add_sub_cancel_left]
  rw [← returned_fst, PMF.bind_map]
  exact export_stage oracle state trace query table beforeOutput ready

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (returned state trace query table beforeOutput).map (exportControl true) := by
  simpa only [packetSteps, Bool.toNat_true, show 2 * n + 4 + 1 = 2 * n + 5 by omega] using
    packet_stage_run oracle state trace query table beforeOutput positive true

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table - 1)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (returned state trace query table beforeOutput).map (exportControl false) := by
  simpa only [Bool.toNat_false, Nat.add_zero,
    show packetSteps query table - 1 = steps query table + (2 * n + 4) by unfold packetSteps; omega] using
    packet_stage_run oracle state trace query table beforeOutput positive false

theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps query table) (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (returned state trace query table beforeOutput).map (fun output => (exportControl true output, packetSteps query table)) := by
  have adjacent : packetSteps query table - 1 + 1 = packetSteps query table := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) (packetSteps query table - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready oracle state trace query table beforeOutput positive, PMF.mem_support_map_iff] at support
        obtain ⟨output, _, rfl⟩ := support
        rfl)
    (by intro control support
        rw [adjacent, packet_run oracle state trace query table beforeOutput positive, PMF.mem_support_map_iff] at support
        obtain ⟨output, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, packet_run oracle state trace query table beforeOutput positive, PMF.map_comp, Function.comp_def] using h

theorem returned_length {State : Type*} {n κ : Nat}
    (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (output : Configuration State × List Bool)
    (support : output ∈ (returned state trace query table beforeOutput).support) : output.2.length = n := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [returned, lookup, PMF.mem_support_pure_iff] at support
      subst output
      exact Bits.length_toList value
  | none =>
      simp only [returned, lookup, PMF.mem_support_map_iff] at support
      obtain ⟨value, _, rfl⟩ := support
      exact Bits.length_toList value

/-- The actual retained frame contains the original cache table or the
physically inserted query/value pair, at the first table cell in both cases.
The left blank produced by cache rewind is kept explicitly. -/
theorem returned_table_layout {State : Type*} {n κ : Nat}
    (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (output : Configuration State × List Bool)
    (support : output ∈ (returned state trace query table beforeOutput).support) :
    ∃ value : Bits n, output.2 = value.toList ∧ output.1.state = state ∧ output.1.reverseTrace = trace ∧
      (match output.1.control with | .running machine => some machine.inputTape | _ => none) =
        some (if (table.lookup query).isSome then
          { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }
        else Tape.ofBits (SimulatorLookup.tableBits ((query, value) :: table))) := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [returned, lookup, PMF.mem_support_pure_iff] at support
      subst output
      refine ⟨value, rfl, rfl, rfl, ?_⟩
      simp only [Option.isSome_some, ↓reduceIte]
      exact SimulatorLookupRestoredHit.finish_table state trace query table beforeOutput value true
  | none =>
      simp only [returned, lookup, PMF.mem_support_map_iff] at support
      obtain ⟨value, _, rfl⟩ := support
      refine ⟨value, rfl, rfl, rfl, ?_⟩
      rfl

/-- Response marginal agrees with the fixed simulator when every absent
query is unrecognized. Recognition is a hypothesis here, not executed code.
The whole retained physical frame is separately specified by packet_run. -/
theorem response_correct {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n)
    (admissible : table.lookup query = none → terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).map
        (fun control => ((NativePacketComponent.read control).1.state,
          (NativePacketComponent.read control).1.reverseTrace, (NativePacketComponent.read control).2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun output => (output.1.2, trace, output.2.toList)) := by
  rw [packet_run oracle state trace query table beforeOutput positive, PMF.map_comp]
  cases lookup : table.lookup query with
  | some value =>
      simp [returned, lookup, compressionSimulator_terminal_eq, PMF.pure_map, exportControl,
        NativePacketComponent.read, SimulatorLookupRestoredHit.finish, CodeRelocation.frame, NativeCode.frame]
  | none =>
      simp [returned, lookup, compressionSimulator_terminal_eq, admissible lookup, PMF.map_comp,
        exportControl, NativePacketComponent.read, CodeRelocation.frame, SimulatorFreshAfterLookupResponse.finish,
        SimulatorFreshResponse.finish, NativeCode.frame, Function.comp_def]

/-- The fixed simulator correspondence also retains the actual physical
updated table at its head. Cache rewind's extra blank is represented, rather
than discarded by a host normalization. Recognition is still an entry condition. -/
theorem response_correct_with_table {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n)
    (admissible : table.lookup query = none → terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).map
        (fun control => ((NativePacketComponent.read control).1.state,
          (NativePacketComponent.read control).1.reverseTrace, (NativePacketComponent.read control).2,
          match (NativePacketComponent.read control).1.control with
          | .running machine => some machine.inputTape | _ => none)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun output => (output.1.2, trace, output.2.toList,
          some (if (table.lookup query).isSome then
            { Tape.ofBits (SimulatorLookup.tableBits output.1.1) with left := [none] }
          else Tape.ofBits (SimulatorLookup.tableBits output.1.1)))) := by
  rw [packet_run oracle state trace query table beforeOutput positive, PMF.map_comp]
  cases lookup : table.lookup query with
  | some value =>
      simp only [returned, PMF.pure_map, Function.comp_def, exportControl, ↓reduceIte,
        NativePacketComponent.read, compressionSimulator_terminal_eq, lookup, Option.isSome_some]
      exact congrArg (fun tape : Option Tape => PMF.pure (state, trace, value.toList, tape))
        (SimulatorLookupRestoredHit.finish_table state trace query table beforeOutput value true)
  | none =>
      simp [returned, lookup, compressionSimulator_terminal_eq, admissible lookup, PMF.map_comp,
        exportControl, NativePacketComponent.read, CodeRelocation.frame, CodeRelocation.control,
        SimulatorFreshAfterLookupResponse.finish, SimulatorFreshResponse.finish,
        SimulatorRememberResponse.finish, NativeCode.frame, Function.comp_def, Configuration.rebasePc]

theorem packetSteps_hit {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (value : Bits n) (hit : table.lookup query = some value) :
    packetSteps query table = SimulatorLookupRestore.steps query table + 3 * n + 9 := by
  simp only [packetSteps, steps, hit, Option.isSome_some, ↓reduceIte, SimulatorLookupRestoredHit.steps]
  omega

theorem packetSteps_missing {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (fresh : table.lookup query = none) :
    packetSteps query table = table.length * (15 * n + 12 * κ + 26) + 18 * n + 9 * κ + 31 := by
  have h := SimulatorFreshAfterLookupResponse.packetSteps_eq table
  unfold SimulatorFreshAfterLookupResponse.packetSteps at h
  simp only [packetSteps, steps, fresh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [show SimulatorLookup.lookupSteps query table + SimulatorFreshAfterLookupResponse.steps table + (2 * n + 5) =
    SimulatorLookup.lookupSteps query table + (SimulatorFreshAfterLookupResponse.steps table + (2 * n + 5)) by omega,
    h, SimulatorLookup.lookupSteps_missing query table fresh]
  ring

/-- A common table-size budget covers both runtime branches. The positive
response width is the existing common-code entry condition. -/
theorem packetSteps_le {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (positive : 0 < n) :
    packetSteps query table ≤ table.length * (15 * n + 12 * κ + 26) + 18 * n + 9 * κ + 31 := by
  cases lookup : table.lookup query with
  | some value =>
      rw [packetSteps_hit query table value lookup]
      have h := SimulatorLookupRestore.steps_le query table
      omega
  | none => exact le_of_eq (packetSteps_missing query table lookup)

/-- Reuse the lookup input; this shared entry contract starts at the first
physical table cell, as required by the missing-branch rewind. -/
structure PacketInput (State : Type*) (n κ : Nat) where
  data : SimulatorLookup.LookupInput State n κ
  empty_prefix : data.beforeInput = []
  positive : 0 < n

noncomputable def packetProcedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (PacketInput State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query input.data.beforeInput input.data.beforeOutput)))
    (fun _ output => exportControl true output)
    (fun input => returned input.data.state input.data.trace input.data.query input.data.table input.data.beforeOutput)
    (fun input => packetSteps input.data.query input.data.table)
    (fun input => by rw [input.empty_prefix, packet_run oracle _ _ _ _ _ input.positive])

theorem packetProcedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (packetProcedure n κ oracle) := by
  apply Procedure.operational_ofFixed

noncomputable def packetHandler {State : Type*} (n κ : Nat) (oracle : BitOracle State) (input : PacketInput State n κ) :
    PacketResponseService.Handler (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.ready where
  execution := (packetProcedure n κ oracle).reindex (fun (_ : Unit) => input)
  ready_exit _ := rfl
  read := NativePacketComponent.read
  read_exit _ := rfl
  responseCap := n
  response_bound := by
    intro output support
    change output ∈ (returned input.data.state input.data.trace input.data.query input.data.table input.data.beforeOutput).support at support
    exact (returned_length _ _ _ _ _ output support).le

theorem packetHandler_exact {State : Type*} (n κ : Nat) (oracle : BitOracle State) (input : PacketInput State n κ) :
    (packetHandler n κ oracle input).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps input.data.query input.data.table)
    (.computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query input.data.beforeInput input.data.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [input.empty_prefix, packet_first_joint oracle _ _ _ _ _ input.positive, PMF.map_comp]
  simp only [packetHandler, packetProcedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    NativePacketComponent.read, exportControl, ↓reduceIte, Function.comp_def]

/-- Count code, retained physical frame and the exporter's working cells
through the actual response return, for every supported intermediate state. -/
theorem packet_encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ packetSteps query table)
    (target : NativePacketComponent.Control State)
    (support : target ∈ (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) elapsed
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, target)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))) (packetSteps query table) := by
  exact NativePacketComponent.encoded_peak E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) (packetSteps query table) elapsed within target support

theorem packet_first_encoded {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (result : NativePacketComponent.Control State × Nat)
    (support : result ∈ (runToBoundary (NativePacketComponent.step (code n κ) oracle)
      NativePacketComponent.readyBoundary (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, result.1)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))) (packetSteps query table) := by
  exact NativePacketComponent.first_encoded E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) NativePacketComponent.readyBoundary (packetSteps query table) result support

end Foundation.Hash.Native.SimulatorLookupDispatch
