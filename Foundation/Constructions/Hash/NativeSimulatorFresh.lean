import Foundation.Constructions.Hash.NativeSimulatorRemember
import Foundation.Crypto.Semantics.Oracle.NativeRandomAppend
import Foundation.Crypto.Semantics.Oracle.CodeRelocation
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources

/-! A single finite native code generates fresh fair bits and physically
prepends the runtime key/value pair to the simulator table. No host table
update, intermediate resume or external randomness capability is executed.
The entry layout retains the blank produced by the existing table rewind. -/
namespace Foundation.Hash.Native.SimulatorFresh
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code (n κ : Nat) : Code :=
  CodeRelocation.host (NativeRandomAppend.code n) (SimulatorRemember.code n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 18 * n + 9 * κ + 16 := by
  simp [code, CodeRelocation.code_length, SimulatorRemember.code_length]; omega

theorem code_native (n κ : Nat) :
    ∀ instruction ∈ code n κ, ∃ native, instruction = .native native := by
  exact CodeRelocation.host_native _ _ (NativeRandomAppend.code_native n) (SimulatorRemember.code_native n κ)

def start {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration where
  inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }
  outputTape := { left := (compressionPacket query).reverse.map some ++ beforeOutput }

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame (2 * n) (NativeCode.frame state trace
    { SimulatorRemember.finish (query, value) table beforeOutput with halted := halt })

def steps (n κ : Nat) : Nat := 2 * n + SimulatorRemember.steps n κ

/-- Adjacent horizons of the same physical execution. The runtime sampled
value is copied into the table by the actual relocated remember code. -/
theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat))
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  rw [TimedExecution.eval_add]
  have draw := NativeRandomAppend.run oracle state trace []
    ((SimulatorRemember.code n κ).map (CodeRelocation.instruction (2 * n)))
    ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
    ((compressionPacket query).reverse.map some ++ beforeOutput) n
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at draw
  have host : NativeRandomAppend.code n ++
      (SimulatorRemember.code n κ).map (CodeRelocation.instruction (2 * n)) = code n κ := by
    simp [code, CodeRelocation.host]
  rw [host] at draw
  change TimedExecution.eval _ (2 * n) _ = _ at draw
  simp only [start] at ⊢
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
    (NativeRandomAppend.code n) (SimulatorRemember.code n κ) oracle
    (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat)
    (NativeCode.frame state trace (SimulatorRemember.startAfterRewind (query, value) table beforeOutput))
  simp_rw [SimulatorRemember.stage_run_after_rewind, PMF.pure_map] at continuation
  simp only [NativeRandomAppend.code_length] at continuation ⊢
  simp only [code]
  simp_rw [continuation]
  rfl

/-- Entry immediately after moving left over the failed-lookup flag.
The old blank on its right is represented, not freely discarded. -/
def startAtFlag {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration :=
  { start query table beforeOutput with outputTape :=
    { left := (compressionPacket query).reverse.map some ++ beforeOutput,
      current := some false, right := [none] } }

/-- A positive-width draw overwrites the flag and consumes the adjacent
blank during its first two actual instructions. Width zero is excluded only
from this alternate entry contract, not from the basic sampler theorem. -/
theorem stage_run_at_flag {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat))
      (NativeCode.frame state trace (startAtFlag query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  have first : TimedExecution.eval (Reification.timedStep (code n κ) oracle) 2
      (NativeCode.frame state trace (startAtFlag query table beforeOutput)) =
      TimedExecution.eval (Reification.timedStep (code n κ) oracle) 2
        (NativeCode.frame state trace (start query table beforeOutput)) := by
    have h := NativeRandomAppend.overwrite_prefix oracle state trace []
      ((SimulatorRemember.code n κ).map (CodeRelocation.instruction (2 * n)))
      ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
      ((compressionPacket query).reverse.map some ++ beforeOutput) n positive (some false)
    simpa only [code, CodeRelocation.host, NativeRandomAppend.code_length, List.nil_append,
      List.length_nil, startAtFlag, start] using h
  have horizon : 2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat) =
      2 + (2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat) - 2) := by omega
  rw [horizon, TimedExecution.eval_add, first, ← TimedExecution.eval_add, ← horizon, stage_run]

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps n κ)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value) := by
  simpa [steps, SimulatorRemember.steps] using stage_run oracle state trace query table beforeOutput true

/-- Actual first native halt, with the shared sampled value, full physical
cache, source cells, external state and transcript in one joint law. -/
theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps n κ)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => (finish state trace query table beforeOutput value, steps n κ)) := by
  have adjacent : steps n κ - 1 + 1 = steps n κ := by unfold steps SimulatorRemember.steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (start query table beforeOutput)) (steps n κ - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput false
        have size : steps n κ - 1 = 2 * n + (5 * n + 7 * (n + κ + 1) + 5) := by
          unfold steps SimulatorRemember.steps; omega
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [size, law, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [adjacent, run, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, run, PMF.map_comp, Function.comp_def] using h

/-- Observe the actual stored table; this is a mathematical observation,
not an executed decoder or an exported digest packet. -/
def storedTable {State : Type*} (frame : Configuration State) : State × List (List Bool × List Bool) × Tape :=
  (frame.state, frame.reverseTrace, match frame.control with | .running machine => machine.inputTape | _ => {})

/-- The real native draw-and-write realizes the cache/state marginal of
the fixed simulator's unrecognized fresh branch. Branch selection is an
explicit hypothesis; recognizing the branch and exporting remain separate. -/
theorem fresh_branch_table {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none)
    (unrecognized : terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps n κ)
      (NativeCode.frame state trace (start query table beforeOutput))).map storedTable =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => (result.1.2, trace, Tape.ofBits (SimulatorLookup.tableBits result.1.1))) := by
  rw [run, compressionSimulator_terminal_eq, fresh, unrecognized, PMF.map_comp, PMF.map_comp]
  rfl

structure Input (State : Type*) (n κ : Nat) where
  state : State
  trace : List (List Bool × List Bool)
  query : CompressionInput (Bits κ) (Bits n)
  table : CompressionTable (Bits κ) (Bits n)
  beforeOutput : List (Option Bool)

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (code n κ) oracle) (Input State n κ) (Configuration State) :=
  TimedExecution.Procedure.ofFixed _
    (fun input => NativeCode.frame input.state input.trace (start input.query input.table input.beforeOutput))
    (fun _ output => output)
    (fun input => (uniform (Bits n)).map (fun value => finish input.state input.trace input.query input.table input.beforeOutput value))
    (fun _ => steps n κ)
    (fun input => by rw [run, PMF.map_comp]; rfl)

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

theorem procedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : Input State n κ) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((procedure n κ oracle).budget input) ((procedure n κ oracle).entry input) =
      (procedure n κ oracle).costed input := by
  change runToBoundary _ _ (steps n κ)
    (NativeCode.frame input.state input.trace (start input.query input.table input.beforeOutput)) = _
  rw [first_joint]
  simp only [procedure, TimedExecution.Procedure.ofFixed, PMF.map_comp, Function.comp_def]

/-- Complete encoded storage, including the old table and retained source.
The general native-only bound also covers every local-randomness branch. -/
theorem encoded_peak {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      elapsed (NativeCode.frame state trace (start query table beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, target)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (start query table beforeOutput))) horizon := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ) (code_native n κ)
    (start query table beforeOutput) horizon elapsed within target support

end Foundation.Hash.Native.SimulatorFresh
