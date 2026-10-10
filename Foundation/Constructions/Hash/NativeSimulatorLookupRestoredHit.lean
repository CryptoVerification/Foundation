import Foundation.Constructions.Hash.NativeSimulatorLookupRestore
import Foundation.Constructions.Hash.NativeSimulatorLookupHitResponse

/-! Cached response with the complete table physically restored before export.
The original search, both return jumps, rewind, flag erasure and packet export
are executed on one retained machine frame. Request preparation is separate. -/
namespace Foundation.Hash.Native.SimulatorLookupRestoredHit
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code (n κ : Nat) : Code := SimulatorLookupRestore.codeWithBody n κ (SimulatorLookupHitResponse.body n)

theorem code_length (n κ : Nat) : (code n κ).length = 11 * n + 2 * κ + 87 := by
  simp [code, SimulatorLookupRestore.codeWithBody_length, SimulatorLookupHitResponse.body_length]; omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ instruction, op = .native instruction := by
  apply SimulatorLookupRestore.codeWithBody_native
  intro op member
  simp only [SimulatorLookupHitResponse.body, StraightLine.code, List.mem_append, List.mem_map,
    List.mem_singleton] at member
  rcases member with ⟨action, _, rfl⟩ | rfl <;> exact ⟨_, rfl⟩

def bodyFinish {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (value : Bits n) (halt : Bool) : Machine.Configuration :=
  { SimulatorLookupRestore.afterRewind query table beforeOutput with pc := n + 3, outputTape := FixedWidthCopy.frontier (none :: (compressionPacket query).reverse.map some ++ beforeOutput) (value.toList.map some ++ [none]), halted := halt }

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
    (CodeRelocation.frame 5 (NativeCode.frame state trace (bodyFinish query table beforeOutput value halt)))

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) : Nat := SimulatorLookupRestore.steps query table + n + 4

theorem body_stage_run_with_tail {State : Type*} {n κ : Nat}
    (tail : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (SimulatorLookupHitResponse.body n ++ tail) oracle) (n + 3 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookupRestore.afterRewind query table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (bodyFinish query table beforeOutput value halt)) := by
  have layout := SimulatorLookup.lookupFinish_output query table [] beforeOutput
  rw [hit] at layout
  simp only [SimulatorLookup.lookupResponse, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] at layout
  have output : (SimulatorLookupRestore.afterRewind query table beforeOutput).outputTape =
      { left := value.toList.reverse.map some ++ some true :: ((compressionPacket query).reverse.map some ++ beforeOutput) } := by
    simpa only [List.append_assoc, List.cons_append, SimulatorLookupRestore.afterRewind,
      NativeBitstringRewind.finish, SimulatorLookup.lookupRewindInput, Configuration.resumeAt] using layout
  have h := NativePacketFlagResponse.stage_run tail oracle state trace
    (SimulatorLookupRestore.afterRewind query table beforeOutput)
    value.toList ((compressionPacket query).reverse.map some ++ beforeOutput) rfl rfl output halt
  simpa only [SimulatorLookupHitResponse.body, List.append_nil, bodyFinish, Bits.length_toList, List.cons_append] using h

theorem body_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (SimulatorLookupHitResponse.body n) oracle) (n + 3 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookupRestore.afterRewind query table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (bodyFinish query table beforeOutput value halt)) := by
  simpa only [List.append_nil] using body_stage_run_with_tail [] oracle state trace query table beforeOutput value hit halt

theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table - 1 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (finish state trace query table beforeOutput value halt) := by
  have size : steps query table - 1 + halt.toNat = SimulatorLookupRestore.steps query table + (n + 3 + halt.toNat) := by
    unfold steps; omega
  rw [size]
  unfold code
  rw [SimulatorLookupRestore.withBody_run, body_stage_run oracle state trace query table beforeOutput value hit halt,
    PMF.pure_map]
  rfl

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (finish state trace query table beforeOutput value) := by
  simpa only [Bool.toNat_true, show steps query table - 1 + 1 = steps query table by unfold steps; omega] using
    stage_run oracle state trace query table beforeOutput value hit true

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (Reification.timedStep (code n κ) oracle) (fun frame => Reification.terminal frame.control)
      (steps query table) (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (finish state trace query table beforeOutput value, steps query table) := by
  have adjacent : steps query table - 1 + 1 = steps query table := by unfold steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) (steps query table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput value hit false
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [law, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
    (by intro frame support
        rw [adjacent, run oracle state trace query table beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  simpa only [adjacent, run oracle state trace query table beforeOutput value hit, PMF.pure_map] using h

theorem finish_table {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool) :
    (match (finish state trace query table beforeOutput value halt).control with
      | .running machine => some machine.inputTape | _ => none) =
      some ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }) := by
  exact congrArg some (SimulatorLookup.lookupRewind_table query table beforeOutput)

theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary (steps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      PMF.pure (.computing (finish state trace query table beforeOutput value), steps query table) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]),
    first_joint oracle state trace query table beforeOutput value hit, PMF.pure_map]

theorem export_stage_with_code {State : Type*} {n κ : Nat}
    (host : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (ready : Bool) :
    TimedExecution.eval (NativePacketComponent.step host oracle) (2 * n + 4 + ready.toNat)
      (.computing (finish state trace query table beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value)
        (if ready then .returned value.toList else .reversing [] value.toList)) := by
  let machine := ((bodyFinish query table beforeOutput value true).rebasePc 5).rebasePc
    (SimulatorLookup.lookupCode n κ).length
  have layout : machine.outputTape.Equivalent
      { (ResponseExport.fromCells (value.toList.map some ++ none :: [])) with
        left := none :: (compressionPacket query).reverse.map some ++ beforeOutput } := Tape.Equivalent.refl _
  cases ready
  · have h := NativePacketComponent.export_prefix_before_ready host oracle state machine trace value.toList
      (none :: (compressionPacket query).reverse.map some ++ beforeOutput) [] rfl rfl layout
    simpa only [finish, machine, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
      Bits.length_toList, Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] using h
  · have h := NativePacketComponent.export_prefix_run host oracle state machine trace value.toList
      (none :: (compressionPacket query).reverse.map some ++ beforeOutput) [] rfl rfl layout
    simpa only [finish, machine, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
      Bits.length_toList, Bool.toNat_true, ↓reduceIte, show 2 * n + 4 + 1 = 2 * n + 5 by omega] using h

theorem export_stage {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (ready : Bool) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 4 + ready.toNat)
      (.computing (finish state trace query table beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value)
        (if ready then .returned value.toList else .reversing [] value.toList)) := by
  exact export_stage_with_code (code n κ) oracle state trace query table beforeOutput value ready

def packetSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := steps query table + (2 * n + 5)

theorem packetSteps_eq {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    packetSteps query table = SimulatorLookupRestore.steps query table + 3 * n + 9 := by
  unfold packetSteps steps; omega

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.returned value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega),
    component_first_joint oracle state trace query table beforeOutput value hit, PMF.pure_bind]
  simpa only [packetSteps, Nat.add_sub_cancel_left, Bool.toNat_true, ↓reduceIte, show 2 * n + 4 + 1 = 2 * n + 5 by omega] using export_stage oracle state trace query table beforeOutput value true

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table - 1)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.reversing [] value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega),
    component_first_joint oracle state trace query table beforeOutput value hit, PMF.pure_bind]
  simpa only [show packetSteps query table - 1 - steps query table = 2 * n + 4 by unfold packetSteps; omega, Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] using
    export_stage oracle state trace query table beforeOutput value false

theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps query table) (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.returned value.toList), packetSteps query table) := by
  have adjacent : packetSteps query table - 1 + 1 = packetSteps query table := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) (packetSteps query table - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready oracle state trace query table beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst control
        rfl)
    (by intro control support
        rw [adjacent, packet_run oracle state trace query table beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst control
        rfl)
  simpa only [adjacent, packet_run oracle state trace query table beforeOutput value hit, PMF.pure_map] using h

/-- The cached branch of the fixed simulator and the actual returned packet
have the same external state, transcript and value. Physical frame retention
is specified by packet_run and finish_input, rather than a host table reset. -/
theorem cached_branch_response {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).map
        (fun control => ((NativePacketComponent.read control).1.state,
          (NativePacketComponent.read control).1.reverseTrace, (NativePacketComponent.read control).2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => (result.1.2, trace, result.2.toList)) := by
  rw [packet_run oracle state trace query table beforeOutput value hit,
    compressionSimulator_terminal_eq, hit, PMF.pure_map]
  simp [NativePacketComponent.read, finish, CodeRelocation.frame, NativeCode.frame, PMF.pure_map]

/-- Keep the existing lookup/hit data; only the rewind's blank-boundary
condition is added. It is an entry obligation, not a free tape preparation. -/
abbrev Input (State : Type*) (n κ : Nat) :=
  { input : SimulatorLookupHitResponse.Input State n κ // input.data.beforeInput = [] }

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (Input State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.val.data.state input.val.data.trace
      (SimulatorLookup.scanStart input.val.data.table input.val.data.query [] input.val.data.beforeOutput)))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun input => PMF.pure
      (finish input.val.data.state input.val.data.trace input.val.data.query input.val.data.table input.val.data.beforeOutput input.val.value,
        input.val.value.toList))
    (fun input => packetSteps input.val.data.query input.val.data.table)
    (fun input => by rw [packet_run oracle _ _ _ _ _ _ input.val.hit, PMF.pure_map])

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

noncomputable def handler {State : Type*} (n κ : Nat) (oracle : BitOracle State) (input : Input State n κ) :
    PacketResponseService.Handler (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.ready where
  execution := (procedure n κ oracle).reindex (fun (_ : Unit) => input)
  ready_exit _ := rfl
  read := NativePacketComponent.read
  read_exit _ := rfl
  responseCap := n
  response_bound := by
    intro output support
    change output ∈ (PMF.pure _).support at support
    rw [PMF.mem_support_pure_iff] at support
    subst output
    simp

theorem handler_exact {State : Type*} (n κ : Nat) (oracle : BitOracle State) (input : Input State n κ) :
    (handler n κ oracle input).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps input.val.data.query input.val.data.table)
    (.computing (NativeCode.frame input.val.data.state input.val.data.trace
      (SimulatorLookup.scanStart input.val.data.table input.val.data.query [] input.val.data.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint oracle _ _ _ _ _ _ input.val.hit, PMF.pure_map]
  simp only [handler, procedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    PMF.pure_map, NativePacketComponent.read, Function.comp_def]

theorem packetSteps_le {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    packetSteps query table ≤ table.length * (15 * n + 12 * κ + 26) + 15 * n + 7 * κ + 32 := by
  have h := SimulatorLookupRestore.steps_le query table
  rw [packetSteps_eq]
  omega

/-- Count code, retained physical frame and the exporter's working cells
through the actual response return, for every supported intermediate state. -/
theorem encoded_peak {State : Type*} {n κ : Nat}
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

theorem first_encoded {State : Type*} {n κ : Nat}
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

end Foundation.Hash.Native.SimulatorLookupRestoredHit
