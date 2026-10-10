import Foundation.Constructions.Hash.NativeSimulatorLookupReturn
import Foundation.Constructions.Hash.NativeSimulatorFreshAfterLookupResponse

/-! Execute the original table lookup, return by an actual native jump,
rewind the same retained table and generate/store a fresh response. The
missing and positive-width conditions are explicit; terminal recognition
and the cache-hit continuation are not implemented by this component. -/
namespace Foundation.Hash.Native.SimulatorLookupFreshResponse
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code (n κ : Nat) : Code := SimulatorLookup.lookupHost n κ (SimulatorFreshAfterLookupResponse.code n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 29 * n + 12 * κ + 103 := by
  simp [code, SimulatorLookup.lookupHost_length, SimulatorFreshAfterLookupResponse.code_length]; omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native := by
  exact HaltReturn.host_native _ _ (SimulatorLookup.lookupCode_native n κ)
    (SimulatorFreshAfterLookupResponse.code_native n κ)

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
    (SimulatorFreshAfterLookupResponse.finish state trace query table beforeOutput value halt)

/-- Exact composition for every continuation horizon, using the physical
configuration produced by the original lookup's compiled return. -/
theorem continuation_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fuel : Nat) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (SimulatorLookup.lookupSteps query table + fuel)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (TimedExecution.eval (Reification.timedStep (SimulatorFreshAfterLookupResponse.code n κ) oracle) fuel
        (NativeCode.frame state trace (SimulatorFreshAfterLookup.start query table beforeOutput))).map
          (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length) := by
  unfold code
  rw [TimedExecution.eval_add, SimulatorLookup.lookup_return_run, PMF.pure_bind]
  have entry : NativeCode.frame state trace
      ((SimulatorLookup.lookupFinish query table [] beforeOutput).resumeAt (SimulatorLookup.lookupCode n κ).length) =
      CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace (SimulatorFreshAfterLookup.start query table beforeOutput)) := by
    simp [SimulatorFreshAfterLookup.start, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
      Machine.Configuration.resumeAt, Machine.Configuration.rebasePc]
  rw [entry]
  exact HaltReturn.body_eval _ _ oracle fuel _

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :=
  SimulatorLookup.lookupSteps query table + SimulatorFreshAfterLookupResponse.steps table

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value) := by
  rw [steps, continuation_run, SimulatorFreshAfterLookupResponse.run oracle state trace query table beforeOutput fresh positive,
    PMF.map_comp]
  rfl

theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table - 1 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  have size : steps query table - 1 + halt.toNat = SimulatorLookup.lookupSteps query table +
      (SimulatorFreshAfterLookup.rewindSteps table + (1 + (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)))) := by
    unfold steps SimulatorFreshAfterLookupResponse.steps SimulatorFreshResponse.steps SimulatorRememberResponse.steps
    omega
  rw [size, continuation_run, SimulatorFreshAfterLookupResponse.stage_run oracle state trace query table beforeOutput fresh positive halt,
    PMF.map_comp]
  rfl

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (uniform (Bits n)).map (fun value => (finish state trace query table beforeOutput value, steps query table)) := by
  have adjacent : steps query table - 1 + 1 = steps query table := by
    unfold steps SimulatorFreshAfterLookupResponse.steps SimulatorFreshResponse.steps SimulatorRememberResponse.steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) (steps query table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput fresh positive false
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [law, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [adjacent, run oracle state trace query table beforeOutput fresh positive, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, run oracle state trace query table beforeOutput fresh positive,
    PMF.map_comp, Function.comp_def] using h


theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
      (steps query table) (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (uniform (Bits n)).map (fun value => (.computing (finish state trace query table beforeOutput value), steps query table)) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]), first_joint oracle state trace query table beforeOutput fresh positive, PMF.map_comp]
  rfl

/-- Export starts at the actual response head reached by the native code.
The original native frame, including the full new table, is retained. -/
theorem export_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 5)
      (.computing (finish state trace query table beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.returned value.toList)) := by
  have exported := NativePacketComponent.export_prefix_run (code n κ) oracle state
    (((SimulatorRememberResponse.finish (query, value) table beforeOutput).rebasePc (2 * n)).rebasePc 1 |>.rebasePc 5 |>.rebasePc (SimulatorLookup.lookupCode n κ).length)
    trace value.toList
    (none :: (compressionPacket query).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, SimulatorFreshAfterLookupResponse.finish, SimulatorFreshResponse.finish, SimulatorRememberResponse.finish, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Bits.length_toList] using exported

theorem export_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 4)
      (.computing (finish state trace query table beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.reversing [] value.toList)) := by
  have exported := NativePacketComponent.export_prefix_before_ready (code n κ) oracle state
    (((SimulatorRememberResponse.finish (query, value) table beforeOutput).rebasePc (2 * n)).rebasePc 1 |>.rebasePc 5 |>.rebasePc (SimulatorLookup.lookupCode n κ).length)
    trace value.toList
    (none :: (compressionPacket query).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, SimulatorFreshAfterLookupResponse.finish, SimulatorFreshResponse.finish, SimulatorRememberResponse.finish, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Bits.length_toList] using exported

def packetSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) := steps query table + (2 * n + 5)

theorem packetSteps_eq {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    packetSteps query table = SimulatorLookup.lookupSteps query table +
      (2 * ((3 * n + 2 * κ + 4) * table.length) + 17 * n + 8 * κ + 26) := by
  have h := SimulatorFreshAfterLookupResponse.packetSteps_eq table
  unfold packetSteps steps SimulatorFreshAfterLookupResponse.packetSteps at *
  omega

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (uniform (Bits n)).map (fun value => .exporting (finish state trace query table beforeOutput value) (.returned value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega), component_first_joint oracle state trace query table beforeOutput fresh positive, PMF.bind_map]
  simp only [Function.comp_def, packetSteps, Nat.add_sub_cancel_left, export_run]
  rfl

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table - 1)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (uniform (Bits n)).map (fun value => .exporting (finish state trace query table beforeOutput value) (.reversing [] value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps query table) _ _ (by unfold packetSteps; omega), component_first_joint oracle state trace query table beforeOutput fresh positive, PMF.bind_map]
  simp only [Function.comp_def, show packetSteps query table - 1 - steps query table = 2 * n + 4 by unfold packetSteps; omega,
    export_before_ready]
  rfl

/-- Exact first response return and retained state share the same runtime
sample. This does not discard the physical table or the old transcript. -/
theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps query table) (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) =
      (uniform (Bits n)).map (fun value =>
        (.exporting (finish state trace query table beforeOutput value) (.returned value.toList), packetSteps query table)) := by
  have adjacent : packetSteps query table - 1 + 1 = packetSteps query table := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) (packetSteps query table - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready oracle state trace query table beforeOutput fresh positive, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro control support
        rw [adjacent, packet_run oracle state trace query table beforeOutput fresh positive, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, packet_run oracle state trace query table beforeOutput fresh positive, PMF.map_comp, Function.comp_def] using h



/-- The exported packet and physical table jointly realize the fixed
simulator's fresh unrecognized branch. The observer only reads the packet
that was actually exported; it does not produce a packet from the table. -/
theorem fresh_branch_response {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n)
    (unrecognized : terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps query table)
      (.computing (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)))).map
        (fun control => (SimulatorFresh.storedTable (NativePacketComponent.read control).1,
          (NativePacketComponent.read control).2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => ((result.1.2, trace, Tape.ofBits (SimulatorLookup.tableBits result.1.1)), result.2.toList)) := by
  rw [packet_run oracle state trace query table beforeOutput fresh positive, compressionSimulator_terminal_eq, fresh, unrecognized, PMF.map_comp, PMF.map_comp]
  rfl

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (SimulatorFreshAfterLookup.Input State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query [] input.data.beforeOutput)))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun input => (uniform (Bits n)).map (fun value =>
      (finish input.data.state input.data.trace input.data.query input.data.table input.data.beforeOutput value, value.toList)))
    (fun input => packetSteps input.data.query input.data.table)
    (fun input => by rw [packet_run oracle _ _ _ _ _ input.fresh input.positive, PMF.map_comp]; rfl)

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

noncomputable def handler {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : SimulatorFreshAfterLookup.Input State n κ) :
    PacketResponseService.Handler (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.ready where
  execution := (procedure n κ oracle).reindex (fun (_ : Unit) => input)
  ready_exit _ := rfl
  read := NativePacketComponent.read
  read_exit _ := rfl
  responseCap := n
  response_bound := by
    intro output support
    change output ∈ ((uniform (Bits n)).map _).support at support
    rw [PMF.mem_support_map_iff] at support
    obtain ⟨value, _, rfl⟩ := support
    simp

theorem handler_exact {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : SimulatorFreshAfterLookup.Input State n κ) :
    (handler n κ oracle input).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps input.data.query input.data.table)
    (.computing (NativeCode.frame input.data.state input.data.trace
      (SimulatorLookup.scanStart input.data.table input.data.query [] input.data.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint oracle _ _ _ _ _ input.fresh input.positive, PMF.map_comp]
  simp only [handler, procedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    PMF.map_comp, NativePacketComponent.read, Function.comp_def]

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

/-- Full missing-branch time, from the original search entry to physical
response readiness. Preparing the input tapes is outside this contract. -/
theorem packetSteps_missing {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (fresh : table.lookup query = none) :
    packetSteps query table = table.length * (15 * n + 12 * κ + 26) + 18 * n + 9 * κ + 31 := by
  rw [packetSteps_eq, SimulatorLookup.lookupSteps_missing query table fresh]
  ring

end Foundation.Hash.Native.SimulatorLookupFreshResponse
