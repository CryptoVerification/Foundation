import Foundation.Constructions.Hash.NativeSimulatorFresh
import Foundation.Constructions.Hash.NativeSimulatorRememberResponse
import Foundation.Crypto.Semantics.Oracle.NativePacketCodeResources

/-! Actual native fair-bit generation, table insertion and physical response
export. The retained table and the returned packet contain the same runtime
sample. The original rewind blank is consumed by the actual insertion code. -/
namespace Foundation.Hash.Native.SimulatorFreshResponse
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code (n κ : Nat) : Code :=
  CodeRelocation.host (NativeRandomAppend.code n) (SimulatorRememberResponse.code n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 19 * n + 10 * κ + 19 := by
  simp [code, CodeRelocation.code_length, SimulatorRememberResponse.code_length]; omega

theorem code_native (n κ : Nat) :
    ∀ instruction ∈ code n κ, ∃ native, instruction = .native native := by
  exact CodeRelocation.host_native _ _ (NativeRandomAppend.code_native n) (SimulatorRememberResponse.code_native n κ)

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame (2 * n) (NativeCode.frame state trace
    { SimulatorRememberResponse.finish (query, value) table beforeOutput with halted := halt })

def steps (n κ : Nat) : Nat := 2 * n + SimulatorRememberResponse.steps n κ

/-- Adjacent horizons of the same physical execution. The runtime sampled
value is copied into the table by the actual relocated remember code. -/
theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat))
      (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  rw [TimedExecution.eval_add]
  have draw := NativeRandomAppend.run oracle state trace []
    ((SimulatorRememberResponse.code n κ).map (CodeRelocation.instruction (2 * n)))
    ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
    ((compressionPacket query).reverse.map some ++ beforeOutput) n
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at draw
  have host : NativeRandomAppend.code n ++
      (SimulatorRememberResponse.code n κ).map (CodeRelocation.instruction (2 * n)) = code n κ := by
    simp [code, CodeRelocation.host]
  rw [host] at draw
  change TimedExecution.eval _ (2 * n) _ = _ at draw
  simp only [SimulatorFresh.start] at ⊢
  rw [draw, PMF.bind_map]
  have placement (value : Bits n) :
      NativeCode.frame state trace
        { pc := 2 * n, inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] },
          outputTape := { left := value.toList.reverse.map some ++ (compressionPacket query).reverse.map some ++ beforeOutput } } =
      CodeRelocation.frame (NativeRandomAppend.code n).length
        (NativeCode.frame state trace (SimulatorRemember.startAfterRewind (query, value) table beforeOutput)) := by
    simp [SimulatorRemember.startAfterRewind, SimulatorRemember.start, CodeRelocation.frame,
      CodeRelocation.control, NativeCode.frame, Configuration.rebasePc,
      List.reverse_append, List.map_append, List.append_assoc]
  simp only [Function.comp_def] at ⊢
  simp only [List.append_assoc] at placement
  simp_rw [placement]
  have continuation (value : Bits n) := CodeRelocation.eval
    (NativeRandomAppend.code n) (SimulatorRememberResponse.code n κ) oracle
    (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)
    (NativeCode.frame state trace (SimulatorRemember.startAfterRewind (query, value) table beforeOutput))
  simp_rw [SimulatorRememberResponse.stage_run_after_rewind, PMF.pure_map] at continuation
  simp only [NativeRandomAppend.code_length] at continuation ⊢
  simp only [code]
  simp_rw [continuation]
  rfl

/-- A positive-width draw overwrites the flag and consumes the adjacent
blank during its first two actual instructions. Width zero is excluded only
from this alternate entry contract, not from the basic sampler theorem. -/
theorem stage_run_at_flag {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat))
      (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  have first : TimedExecution.eval (Reification.timedStep (code n κ) oracle) 2
      (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)) =
      TimedExecution.eval (Reification.timedStep (code n κ) oracle) 2
        (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)) := by
    have h := NativeRandomAppend.overwrite_prefix oracle state trace []
      ((SimulatorRememberResponse.code n κ).map (CodeRelocation.instruction (2 * n)))
      ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
      ((compressionPacket query).reverse.map some ++ beforeOutput) n positive (some false)
    simpa only [code, CodeRelocation.host, NativeRandomAppend.code_length, List.nil_append,
      List.length_nil, SimulatorFresh.startAtFlag, SimulatorFresh.start] using h
  have horizon : 2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat) =
      2 + (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat) - 2) := by omega
  rw [horizon, TimedExecution.eval_add, first, ← TimedExecution.eval_add, ← horizon, stage_run]

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps n κ)
      (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value) := by
  simpa [steps, SimulatorRememberResponse.steps] using stage_run oracle state trace query table beforeOutput true

/-- Actual first native halt, with the shared sampled value, full physical
cache, source cells, external state and transcript in one joint law. -/
theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps n κ)
      (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => (finish state trace query table beforeOutput value, steps n κ)) := by
  have adjacent : steps n κ - 1 + 1 = steps n κ := by unfold steps SimulatorRememberResponse.steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)) (steps n κ - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput false
        have size : steps n κ - 1 = 2 * n + (5 * n + 8 * (n + κ + 1) + 7) := by
          unfold steps SimulatorRememberResponse.steps; omega
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [size, law, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [adjacent, run, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, run, PMF.map_comp, Function.comp_def] using h


theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
      (steps n κ) (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput))) =
      (uniform (Bits n)).map (fun value => (.computing (finish state trace query table beforeOutput value), steps n κ)) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]), first_joint, PMF.map_comp]
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
    ((SimulatorRememberResponse.finish (query, value) table beforeOutput).rebasePc (2 * n))
    trace value.toList
    (none :: (compressionPacket query).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, SimulatorRememberResponse.finish, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Bits.length_toList] using exported

theorem export_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 4)
      (.computing (finish state trace query table beforeOutput value)) =
      PMF.pure (.exporting (finish state trace query table beforeOutput value) (.reversing [] value.toList)) := by
  have exported := NativePacketComponent.export_prefix_before_ready (code n κ) oracle state
    ((SimulatorRememberResponse.finish (query, value) table beforeOutput).rebasePc (2 * n))
    trace value.toList
    (none :: (compressionPacket query).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (Tape.Equivalent.refl _)
  simpa only [finish, SimulatorRememberResponse.finish, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Bits.length_toList] using exported

def packetSteps (n κ : Nat) := steps n κ + (2 * n + 5)

theorem packetSteps_eq (n κ : Nat) : packetSteps n κ = 17 * n + 8 * κ + 21 := by
  unfold packetSteps steps SimulatorRememberResponse.steps
  omega

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps n κ)
      (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput))) =
      (uniform (Bits n)).map (fun value => .exporting (finish state trace query table beforeOutput value) (.returned value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps n κ) _ _ (by unfold packetSteps; omega), component_first_joint, PMF.bind_map]
  simp only [Function.comp_def, packetSteps, Nat.add_sub_cancel_left, export_run]
  rfl

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps n κ - 1)
      (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput))) =
      (uniform (Bits n)).map (fun value => .exporting (finish state trace query table beforeOutput value) (.reversing [] value.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps n κ) _ _ (by unfold packetSteps; omega), component_first_joint, PMF.bind_map]
  simp only [Function.comp_def, show packetSteps n κ - 1 - steps n κ = 2 * n + 4 by unfold packetSteps; omega,
    export_before_ready]
  rfl

/-- Exact first response return and retained state share the same runtime
sample. This does not discard the physical table or the old transcript. -/
theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps n κ) (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput))) =
      (uniform (Bits n)).map (fun value =>
        (.exporting (finish state trace query table beforeOutput value) (.returned value.toList), packetSteps n κ)) := by
  have adjacent : packetSteps n κ - 1 + 1 = packetSteps n κ := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput))) (packetSteps n κ - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro control support
        rw [adjacent, packet_run, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, packet_run, PMF.map_comp, Function.comp_def] using h

/-- The exported packet and physical table jointly realize the fixed
simulator's fresh unrecognized branch. The observer only reads the packet
that was actually exported; it does not produce a packet from the table. -/
theorem fresh_branch_response {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none)
    (unrecognized : terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps n κ)
      (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)))).map
        (fun control => (SimulatorFresh.storedTable (NativePacketComponent.read control).1,
          (NativePacketComponent.read control).2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => ((result.1.2, trace, Tape.ofBits (SimulatorLookup.tableBits result.1.1)), result.2.toList)) := by
  rw [packet_run, compressionSimulator_terminal_eq, fresh, unrecognized, PMF.map_comp, PMF.map_comp]
  rfl

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (SimulatorFresh.Input State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.state input.trace
      (SimulatorFresh.start input.query input.table input.beforeOutput)))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun input => (uniform (Bits n)).map (fun value =>
      (finish input.state input.trace input.query input.table input.beforeOutput value, value.toList)))
    (fun _ => packetSteps n κ)
    (fun input => by rw [packet_run, PMF.map_comp]; rfl)

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

noncomputable def handler {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : SimulatorFresh.Input State n κ) :
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
    (input : SimulatorFresh.Input State n κ) :
    (handler n κ oracle input).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps n κ)
    (.computing (NativeCode.frame input.state input.trace
      (SimulatorFresh.start input.query input.table input.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint, PMF.map_comp]
  simp only [handler, procedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    PMF.map_comp, NativePacketComponent.read, Function.comp_def]

/-- Count code, retained physical frame and the exporter's working cells
through the actual response return, for every supported intermediate state. -/
theorem encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ packetSteps n κ)
    (target : NativePacketComponent.Control State)
    (support : target ∈ (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) elapsed
      (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, target)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)))) (packetSteps n κ) := by
  exact NativePacketComponent.encoded_peak E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) (packetSteps n κ) elapsed within target support

theorem first_encoded {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (result : NativePacketComponent.Control State × Nat)
    (support : result ∈ (runToBoundary (NativePacketComponent.step (code n κ) oracle)
      NativePacketComponent.readyBoundary (packetSteps n κ)
      (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, result.1)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorFresh.start query table beforeOutput)))) (packetSteps n κ) := by
  exact NativePacketComponent.first_encoded E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) NativePacketComponent.readyBoundary (packetSteps n κ) result support

end Foundation.Hash.Native.SimulatorFreshResponse
