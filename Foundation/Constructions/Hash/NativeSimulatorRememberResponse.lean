import Foundation.Constructions.Hash.NativeSimulatorRemember
import Foundation.Crypto.Semantics.Oracle.NativePacketSuffix
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentPrefix
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources
import Foundation.Crypto.Semantics.Oracle.NativePacketCodeResources
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime

/-! Physical table insertion followed by positioning the stored response for
export. The input table retains the full key. The redundant last output key
cell is erased to create the exporter's adjacent blank delimiter. -/
namespace Foundation.Hash.Native.SimulatorRememberResponse
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def haltPc (n κ : Nat) := SimulatorRemember.haltPc n κ + (n + κ + 1) + 2
def faultPc (n κ : Nat) := haltPc n κ + 1
def tail (n κ : Nat) : Code :=
  StraightLine.code (NativePacketSuffix.actions (n + κ + 1)) ++ [.native .halt, .native .halt]
def code (n κ : Nat) : Code :=
  SimulatorRemember.codeWithContinuation n κ (faultPc n κ) (tail n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 17 * n + 10 * κ + 19 := by
  simp [code, SimulatorRemember.codeWithContinuation_length, tail, StraightLine.code,
    SimulatorRemember.haltPc, SimulatorRemember.keyPc]; omega

theorem code_native (n κ : Nat) :
    ∀ instruction ∈ code n κ, ∃ native, instruction = .native native := by
  apply SimulatorRemember.codeWithContinuation_native
  intro instruction member
  simp only [tail, List.mem_append, StraightLine.code, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with mapped | rfl | rfl
  · obtain ⟨action, _, rfl⟩ := mapped
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

def finish {n κ : Nat} (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration where
  pc := haltPc n κ
  inputTape := Tape.ofBits (SimulatorLookup.tableBits (entry :: table))
  outputTape := FixedWidthCopy.frontier
    (none :: (compressionPacket entry.1).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    (entry.2.toList.map some ++ [none])
  halted := true

theorem postlude_execute {n κ : Nat}
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    StraightLine.execute (NativePacketSuffix.actions (n + κ + 1))
      { SimulatorRemember.finish entry table beforeOutput with halted := false } =
      { finish entry table beforeOutput with halted := false } := by
  have nonempty : compressionPacket entry.1 ≠ [] := by
    intro empty
    have size := compressionPacket_length entry.1
    rw [empty] at size
    simp at size
  have split := List.dropLast_append_getLast nonempty
  have size : (compressionPacket entry.1).dropLast.length + 1 = n + κ + 1 := by
    simp [List.length_dropLast, compressionPacket_length]
  have run := NativePacketSuffix.execute (SimulatorRemember.haltPc n κ)
    (Tape.ofBits (SimulatorLookup.tableBits (entry :: table))) beforeOutput
    (compressionPacket entry.1).dropLast entry.2.toList ((compressionPacket entry.1).getLast nonempty)
  rw [size, split] at run
  simpa only [SimulatorRemember.finish, finish, haltPc] using run

private theorem halt_instruction (n κ : Nat) : (code n κ)[haltPc n κ]? = some (.native .halt) := by
  have fetched := SimulatorRemember.continuation_instruction n κ (faultPc n κ) (tail n κ) (n + κ + 1 + 2)
  have size : (StraightLine.code (NativePacketSuffix.actions (n + κ + 1))).length = n + κ + 1 + 2 := by
    simp [StraightLine.code]
  have last : (tail n κ)[n + κ + 1 + 2]? = some (.native .halt) := by
    unfold tail
    rw [← size, List.getElem?_append_right (by omega), Nat.sub_self]
    rfl
  rw [last] at fetched
  simpa only [code, haltPc, Nat.add_assoc] using fetched

/-- Position the response and execute the optional final halt, in the same
absolute host code used by both table insertion entry contracts. -/
theorem postlude_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (n + κ + 1 + 2 + halt.toNat)
      (NativeCode.frame state trace { SimulatorRemember.finish entry table beforeOutput with halted := false }) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := halt }) := by
  let leading := SimulatorRemember.codeWithContinuation n κ (faultPc n κ) []
  have move := StraightLine.public_run oracle state trace leading [.native .halt, .native .halt]
    (NativePacketSuffix.actions (n + κ + 1))
    { SimulatorRemember.finish entry table beforeOutput with halted := false }
    (by simp [leading, SimulatorRemember.finish, SimulatorRemember.codeWithContinuation_length]) rfl
  have host : leading ++ StraightLine.code (NativePacketSuffix.actions (n + κ + 1)) ++
      [.native .halt, .native .halt] = code n κ := by
    simp [leading, code, tail, SimulatorRemember.codeWithContinuation, List.append_assoc]
  rw [host, NativePacketSuffix.actions_length, postlude_execute] at move
  rw [TimedExecution.eval_add]
  change TimedExecution.eval _ (n + κ + 1 + 2) _ = _ at move
  simp only [NativeCode.frame] at ⊢
  rw [move, PMF.pure_bind]
  have stopped := halt_instruction n κ
  cases halt <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, finish, stopped, Machine.Instruction.next]

/-- Same full native code, immediately before and after its actual halt. -/
theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)
      (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := halt }) := by
  have write := SimulatorRemember.continuation_run oracle state trace entry table beforeOutput
    (faultPc n κ) (tail n κ)
  change TimedExecution.eval (Reification.timedStep (code n κ) oracle) _ _ = _ at write
  rw [show 5 * n + 8 * (n + κ + 1) + 7 + halt.toNat =
    (5 * n + 7 * (n + κ + 1) + 5) + (n + κ + 1 + 2 + halt.toNat) by omega,
    TimedExecution.eval_add, write, PMF.pure_bind, postlude_run]

/-- Same full native code, immediately before and after its actual halt. -/
theorem stage_run_after_rewind {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)
      (NativeCode.frame state trace (SimulatorRemember.startAfterRewind entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace { finish entry table beforeOutput with halted := halt }) := by
  have write := SimulatorRemember.continuation_run_after_rewind oracle state trace entry table beforeOutput
    (faultPc n κ) (tail n κ)
  change TimedExecution.eval (Reification.timedStep (code n κ) oracle) _ _ = _ at write
  rw [show 5 * n + 8 * (n + κ + 1) + 7 + halt.toNat =
    (5 * n + 7 * (n + κ + 1) + 5) + (n + κ + 1 + 2 + halt.toNat) by omega,
    TimedExecution.eval_add, write, PMF.pure_bind, postlude_run]

def steps (n κ : Nat) := 5 * n + 8 * (n + κ + 1) + 8

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps n κ)
      (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (finish entry table beforeOutput)) := by
  simpa [steps, finish] using stage_run oracle state trace entry table beforeOutput true

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps n κ)
      (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)) =
      PMF.pure (NativeCode.frame state trace (finish entry table beforeOutput), steps n κ) := by
  have adjacent : steps n κ - 1 + 1 = steps n κ := by unfold steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)) (steps n κ - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace entry table beforeOutput false
        have size : steps n κ - 1 = 5 * n + 8 * (n + κ + 1) + 7 := by unfold steps; omega
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [size, law, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
    (by intro frame support
        rw [adjacent, run, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  simpa only [adjacent, run, PMF.pure_map] using h

private theorem export_layout {n κ : Nat}
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    (finish entry table beforeOutput).outputTape.Equivalent
      { (ResponseExport.fromCells (entry.2.toList.map some ++ [none])) with left := none :: (compressionPacket entry.1).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput } := by
  exact Tape.Equivalent.refl _

theorem export_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 5)
      (.computing (NativeCode.frame state trace (finish entry table beforeOutput))) =
      PMF.pure (.exporting (NativeCode.frame state trace (finish entry table beforeOutput)) (.returned entry.2.toList)) := by
  simpa only [Bits.length_toList, NativeCode.frame] using NativePacketComponent.export_prefix_run (code n κ) oracle state
    (finish entry table beforeOutput) trace entry.2.toList
    (none :: (compressionPacket entry.1).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (export_layout entry table beforeOutput)

theorem export_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 4)
      (.computing (NativeCode.frame state trace (finish entry table beforeOutput))) =
      PMF.pure (.exporting (NativeCode.frame state trace (finish entry table beforeOutput)) (.reversing [] entry.2.toList)) := by
  simpa only [Bits.length_toList, NativeCode.frame] using NativePacketComponent.export_prefix_before_ready (code n κ) oracle state
    (finish entry table beforeOutput) trace entry.2.toList
    (none :: (compressionPacket entry.1).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore beforeOutput)
    [] rfl rfl (export_layout entry table beforeOutput)

theorem component_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
      (steps n κ) (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) =
      PMF.pure (.computing (NativeCode.frame state trace (finish entry table beforeOutput)), steps n κ) := by
  rw [runToBoundary_map (Reification.timedStep (code n κ) oracle) (NativePacketComponent.step (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]), first_joint, PMF.pure_map]

def packetSteps (n κ : Nat) := steps n κ + (2 * n + 5)

theorem packet_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps n κ)
      (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) =
      PMF.pure (.exporting (NativeCode.frame state trace (finish entry table beforeOutput)) (.returned entry.2.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps n κ) _ _ (by unfold packetSteps; omega), component_first_joint, PMF.pure_bind]
  simp only [packetSteps, Nat.add_sub_cancel_left, export_run]

theorem packet_before_ready {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (packetSteps n κ - 1)
      (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) =
      PMF.pure (.exporting (NativeCode.frame state trace (finish entry table beforeOutput)) (.reversing [] entry.2.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.boundary
    (steps n κ) _ _ (by unfold packetSteps; omega), component_first_joint, PMF.pure_bind]
  rw [show packetSteps n κ - 1 - steps n κ = 2 * n + 4 by unfold packetSteps; omega, export_before_ready]

/-- First actual returned packet, jointly with the physical updated table. -/
theorem packet_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    runToBoundary (NativePacketComponent.step (code n κ) oracle) NativePacketComponent.readyBoundary
      (packetSteps n κ) (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) =
      PMF.pure (.exporting (NativeCode.frame state trace (finish entry table beforeOutput)) (.returned entry.2.toList), packetSteps n κ) := by
  have adjacent : packetSteps n κ - 1 + 1 = packetSteps n κ := by unfold packetSteps; omega
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step (code n κ) oracle)
    NativePacketComponent.readyBoundary
    (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) (packetSteps n κ - 1)
    (NativePacketComponent.ready_absorbing (code n κ) oracle)
    (by intro control support
        rw [packet_before_ready, PMF.mem_support_pure_iff] at support
        subst control; rfl)
    (by intro control support
        rw [adjacent, packet_run, PMF.mem_support_pure_iff] at support
        subst control; rfl)
  simpa only [adjacent, packet_run, PMF.pure_map] using h

/-- Register physical insertion and export with the existing packet service. -/
noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (NativePacketComponent.step (code n κ) oracle)
      (SimulatorRemember.Input State n κ) (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun input => .computing (NativeCode.frame input.state input.trace
      (SimulatorRemember.start input.entry input.table input.beforeOutput)))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun input => PMF.pure (NativeCode.frame input.state input.trace
      (finish input.entry input.table input.beforeOutput), input.entry.2.toList))
    (fun _ => packetSteps n κ)
    (fun input => by rw [packet_run, PMF.pure_map])

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

noncomputable def handler {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : SimulatorRemember.Input State n κ) :
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
    simp only [Bits.length_toList, le_refl]


theorem handler_exact {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : SimulatorRemember.Input State n κ) :
    (handler n κ oracle input).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (packetSteps n κ)
    (.computing (NativeCode.frame input.state input.trace
      (SimulatorRemember.start input.entry input.table input.beforeOutput)))).map
    (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint, PMF.pure_map]
  simp only [handler, procedure, TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed, PMF.pure_map,
    NativePacketComponent.read, Function.comp_def]

/-- Storage of every native intermediate frame, including both physical
copies of the entry. Export-controller storage is a separate bound. -/
theorem encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (elapsed : Nat) (within : elapsed ≤ steps n κ) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle) elapsed
      (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, target)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput))) (steps n κ) := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ) (code_native n κ)
    _ (steps n κ) elapsed within target support

/-- Count code, retained physical frame and the exporter's working cells
through the actual response return, for every supported intermediate state. -/
theorem packet_encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ packetSteps n κ)
    (target : NativePacketComponent.Control State)
    (support : target ∈ (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) elapsed
      (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, target)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)))) (packetSteps n κ) := by
  exact NativePacketComponent.encoded_peak E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) (packetSteps n κ) elapsed within target support

theorem packet_first_encoded {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (result : NativePacketComponent.Control State × Nat)
    (support : result ∈ (runToBoundary (NativePacketComponent.step (code n κ) oracle)
      NativePacketComponent.readyBoundary (packetSteps n κ)
      (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)))).support) :
    ((NativePacketComponent.fullEncoding E).encode (code n κ, result.1)).length ≤
      NativePacketComponent.storageBound (code n κ)
        (NativePacketComponent.Resources.size stateSize
          (.computing (NativeCode.frame state trace (SimulatorRemember.start entry table beforeOutput)))) (packetSteps n κ) := by
  exact NativePacketComponent.first_encoded E stateSize hState oracle (code n κ) (code_native n κ)
    _ (by trivial) NativePacketComponent.readyBoundary (packetSteps n κ) result support

end Foundation.Hash.Native.SimulatorRememberResponse
