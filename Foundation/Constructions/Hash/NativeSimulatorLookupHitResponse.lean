import Foundation.Constructions.Hash.NativeSimulatorLookupReturn
import Foundation.Constructions.Hash.OracleWorlds
import Foundation.Crypto.Semantics.Oracle.NativePacketFlagResponse
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentPrefix
import Foundation.Crypto.Semantics.Oracle.NativePacketCodeResources
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime

/-! The cache-hit branch executes the original lookup, jumps to a physical
flag-erasure/response-positioning continuation, and exports the copied value.
No host lookup or synthetic response is executed. -/
namespace Foundation.Hash.Native.SimulatorLookupHitResponse
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def body (n : Nat) : Code := StraightLine.code (NativePacketFlagResponse.actions n) ++ [.native .halt]
def code (n κ : Nat) : Code := SimulatorLookup.lookupHost n κ (body n)

theorem body_length (n : Nat) : (body n).length = n + 4 := by
  simp [body, StraightLine.code]

theorem code_length (n κ : Nat) : (code n κ).length = 11 * n + 2 * κ + 82 := by
  simp [code, SimulatorLookup.lookupHost_length, body_length]; omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native := by
  apply HaltReturn.host_native _ _ (SimulatorLookup.lookupCode_native n κ)
  intro op member
  simp only [body, StraightLine.code, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨action, _, rfl⟩ | rfl <;> exact ⟨_, rfl⟩

def bodyFinish {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput : List (Option Bool))
    (value : Bits n) (halt : Bool) : Machine.Configuration :=
  { SimulatorLookup.lookupFinish query table beforeInput beforeOutput with pc := n + 3, outputTape := FixedWidthCopy.frontier (none :: (compressionPacket query).reverse.map some ++ beforeOutput) (value.toList.map some ++ [none]), halted := halt }

theorem body_execute {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput : List (Option Bool))
    (value : Bits n) (hit : table.lookup query = some value) :
    StraightLine.execute (NativePacketFlagResponse.actions n)
      ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0) =
      bodyFinish query table beforeInput beforeOutput value false := by
  have layout := SimulatorLookup.lookupFinish_output query table beforeInput beforeOutput
  rw [hit] at layout
  simp only [SimulatorLookup.lookupResponse, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] at layout
  have shape : (SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0 =
      { (SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0 with
        outputTape := { left := value.toList.reverse.map some ++ some true ::
          (compressionPacket query).reverse.map some ++ beforeOutput } } := by
    simp only [Configuration.resumeAt, layout, List.append_assoc, List.cons_append]
  rw [shape]
  have moved := NativePacketFlagResponse.execute
    ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0)
    value.toList ((compressionPacket query).reverse.map some ++ beforeOutput)
  simpa only [Bits.length_toList, bodyFinish, Configuration.resumeAt, Nat.zero_add,
    List.cons_append, List.append_assoc] using moved

theorem body_stage_run_with_tail {State : Type*} {n κ : Nat} (tail : Code)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n)
    (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (body n ++ tail) oracle) (n + 3 + halt.toNat)
      (NativeCode.frame state trace ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0)) =
      PMF.pure (NativeCode.frame state trace (bodyFinish query table beforeInput beforeOutput value halt)) := by
  have layout := SimulatorLookup.lookupFinish_output query table beforeInput beforeOutput
  rw [hit] at layout
  simp only [SimulatorLookup.lookupResponse, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] at layout
  have h := NativePacketFlagResponse.stage_run tail oracle state trace
    ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0)
    value.toList ((compressionPacket query).reverse.map some ++ beforeOutput) rfl rfl layout halt
  simpa only [body, bodyFinish, Bits.length_toList, Configuration.resumeAt, List.cons_append] using h

theorem body_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n)
    (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (body n) oracle) (n + 3 + halt.toNat)
      (NativeCode.frame state trace ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0)) =
      PMF.pure (NativeCode.frame state trace (bodyFinish query table beforeInput beforeOutput value halt)) := by
  simpa only [List.append_nil] using body_stage_run_with_tail [] oracle state trace query table beforeInput beforeOutput value hit halt

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
    (NativeCode.frame state trace (bodyFinish query table beforeInput beforeOutput value halt))

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := SimulatorLookup.lookupSteps query table + n + 4

theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n)
    (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table - 1 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)) =
      PMF.pure (finish state trace query table beforeInput beforeOutput value halt) := by
  rw [show steps query table - 1 + halt.toNat = SimulatorLookup.lookupSteps query table + (n + 3 + halt.toNat) by unfold steps; omega]
  unfold code
  rw [TimedExecution.eval_add, SimulatorLookup.lookup_return_run, PMF.pure_bind]
  have entry : NativeCode.frame state trace
      ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt (SimulatorLookup.lookupCode n κ).length) =
      CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0)) := by
    simp [NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Configuration.resumeAt, Configuration.rebasePc]
  unfold SimulatorLookup.lookupHost
  rw [entry, HaltReturn.body_eval, body_stage_run oracle state trace query table beforeInput beforeOutput value hit halt,
    PMF.pure_map]
  rfl

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)) =
      PMF.pure (finish state trace query table beforeInput beforeOutput value) := by
  simpa only [Bool.toNat_true, show steps query table - 1 + 1 = steps query table by unfold steps; omega] using
    stage_run oracle state trace query table beforeInput beforeOutput value hit true

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (Reification.timedStep (code n κ) oracle) (fun frame => Reification.terminal frame.control)
      (steps query table) (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)) =
      PMF.pure (finish state trace query table beforeInput beforeOutput value, steps query table) := by
  have adjacent : steps query table - 1 + 1 = steps query table := by unfold steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)) (steps query table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeInput beforeOutput value hit false
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [law, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
    (by intro frame support
        rw [adjacent, run oracle state trace query table beforeInput beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  simpa only [adjacent, run oracle state trace query table beforeInput beforeOutput value hit, PMF.pure_map] using h

theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary (steps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput))) =
      PMF.pure (.computing (finish state trace query table beforeInput beforeOutput value), steps query table) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]),
    first_joint oracle state trace query table beforeInput beforeOutput value hit, PMF.pure_map]

theorem export_run_with_code {State : Type*} {n κ : Nat} (host : Code)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step host oracle) (2 * n + 5)
      (.computing (finish state trace query table beforeInput beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.returned value.toList)) := by
  have h := NativePacketComponent.export_prefix_run host oracle state
    ((bodyFinish query table beforeInput beforeOutput value true).rebasePc (SimulatorLookup.lookupCode n κ).length)
    trace value.toList (none :: (compressionPacket query).reverse.map some ++ beforeOutput) [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Bits.length_toList] using h

theorem export_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 5)
      (.computing (finish state trace query table beforeInput beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.returned value.toList)) := by
  exact export_run_with_code (code n κ) oracle state trace query table beforeInput beforeOutput value

theorem export_before_ready_with_code {State : Type*} {n κ : Nat} (host : Code)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step host oracle) (2 * n + 4)
      (.computing (finish state trace query table beforeInput beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.reversing [] value.toList)) := by
  have h := NativePacketComponent.export_prefix_before_ready host oracle state
    ((bodyFinish query table beforeInput beforeOutput value true).rebasePc (SimulatorLookup.lookupCode n κ).length)
    trace value.toList (none :: (compressionPacket query).reverse.map some ++ beforeOutput) [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Bits.length_toList] using h

theorem export_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 4)
      (.computing (finish state trace query table beforeInput beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.reversing [] value.toList)) := by
  exact export_before_ready_with_code (code n κ) oracle state trace query table beforeInput beforeOutput value

def packetSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := steps query table + (2 * n + 5)

theorem packetSteps_eq {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    packetSteps query table = SimulatorLookup.lookupSteps query table + 3 * n + 9 := by
  unfold packetSteps steps; omega

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.returned value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega),
    component_first_joint oracle state trace query table beforeInput beforeOutput value hit, PMF.pure_bind]
  simpa only [packetSteps, Nat.add_sub_cancel_left] using export_run oracle state trace query table beforeInput beforeOutput value

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table - 1)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.reversing [] value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega),
    component_first_joint oracle state trace query table beforeInput beforeOutput value hit, PMF.pure_bind]
  simpa only [show packetSteps query table - 1 - steps query table = 2 * n + 4 by unfold packetSteps; omega] using
    export_before_ready oracle state trace query table beforeInput beforeOutput value

theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps query table) (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput))) =
      PMF.pure (.exporting (finish state trace query table beforeInput beforeOutput value) (.returned value.toList), packetSteps query table) := by
  have adjacent : packetSteps query table - 1 + 1 = packetSteps query table := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput))) (packetSteps query table - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready oracle state trace query table beforeInput beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst control
        rfl)
    (by intro control support
        rw [adjacent, packet_run oracle state trace query table beforeInput beforeOutput value hit, PMF.mem_support_pure_iff] at support
        subst control
        rfl)
  simpa only [adjacent, packet_run oracle state trace query table beforeInput beforeOutput value hit, PMF.pure_map] using h

/-- Positioning and export retain the full physical input tape produced
by lookup. In particular they do not overwrite or reconstruct table cells. -/
theorem finish_input {State : Type*} {n κ : Nat}
    (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool) :
    (match (finish state trace query table beforeInput beforeOutput value halt).control with
      | .running machine => some machine.inputTape | _ => none) =
      some (SimulatorLookup.lookupFinish query table beforeInput beforeOutput).inputTape := rfl

/-- The cached branch of the fixed simulator and the actual returned packet
have the same external state, transcript and value. Physical frame retention
is specified by packet_run and finish_input, rather than a host table reset. -/
theorem cached_branch_response {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)))).map
        (fun control => ((NativePacketComponent.read control).1.state,
          (NativePacketComponent.read control).1.reverseTrace, (NativePacketComponent.read control).2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => (result.1.2, trace, result.2.toList)) := by
  rw [packet_run oracle state trace query table beforeInput beforeOutput value hit,
    compressionSimulator_terminal_eq, hit, PMF.pure_map]
  simp [NativePacketComponent.read, finish, CodeRelocation.frame, NativeCode.frame, PMF.pure_map]

/-- Reuse the existing physical lookup input instead of duplicating its
table, query, state and tape-prefix fields. Only the hit evidence is new. -/
structure Input (State : Type*) (n κ : Nat) where
  data : SimulatorLookup.LookupInput State n κ
  value : Bits n
  hit : data.table.lookup data.query = some value

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (Input State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query input.data.beforeInput input.data.beforeOutput)))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun input => PMF.pure
      (finish input.data.state input.data.trace input.data.query input.data.table input.data.beforeInput input.data.beforeOutput input.value,
        input.value.toList))
    (fun input => packetSteps input.data.query input.data.table)
    (fun input => by rw [packet_run oracle _ _ _ _ _ _ _ input.hit, PMF.pure_map])

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
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps input.data.query input.data.table)
    (.computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query input.data.beforeInput input.data.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint oracle _ _ _ _ _ _ _ input.hit, PMF.pure_map]
  simp only [handler, procedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    PMF.pure_map, NativePacketComponent.read, Function.comp_def]

/-- Count code, retained physical frame and the exporter's working cells
through the actual response return, for every supported intermediate state. -/
theorem encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ packetSteps query table)
    (target : NativePacketComponent.Control State)
    (support : target ∈ (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) elapsed
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, target)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)))) (packetSteps query table) := by
  exact NativePacketComponent.encoded_peak E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) (packetSteps query table) elapsed within target support

theorem first_encoded {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (result : NativePacketComponent.Control State × Nat)
    (support : result ∈ (runToBoundary (NativePacketComponent.step (code n κ) oracle)
      NativePacketComponent.readyBoundary (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, result.1)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)))) (packetSteps query table) := by
  exact NativePacketComponent.first_encoded E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) NativePacketComponent.readyBoundary (packetSteps query table) result support

end Foundation.Hash.Native.SimulatorLookupHitResponse
