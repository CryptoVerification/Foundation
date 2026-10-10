import Foundation.Constructions.Hash.NativeSimulatorDispatchQueryLoading

/-! One physical controller admits a raw request, writes it, executes the
cache-or-local-uniform code, then scans and reverses its response. The table
is retained throughout. Terminal recognition is not implemented here. -/
namespace Foundation.Hash.Native.SimulatorQueryPacket
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev code := SimulatorDispatchQueryLoading.code

inductive Control (State : Type*) where
  | admitting (state : State) (machine : Machine.Configuration)
      (trace : List (List Bool × List Bool)) (request : List Bool)
  | running (component : NativePacketComponent.Control State)

noncomputable def step {State : Type*} (n κ : Nat) (oracle : BitOracle State) : Control State → PMF (Control State)
  | .admitting state machine trace request => PMF.pure (.running (.computing
      (SimulatorQueryLoading.loadingFrame n κ state machine trace request)))
  | .running component => (NativePacketComponent.step (code n κ) oracle component).map .running

def embed {State : Type*} : SimulatorQueryLoading.Control State → Control State
  | .admitting state machine trace request => .admitting state machine trace request
  | .executing frame => .running (.computing frame)

def nativeBoundary {State : Type*} : Control State → Bool
  | .admitting .. => false
  | .running component => NativePacketComponent.boundary component

def ready {State : Type*} : Control State → Option (Configuration State × List Bool)
  | .admitting .. => none
  | .running component => NativePacketComponent.ready component

def readyBoundary {State : Type*} (control : Control State) : Bool := (ready control).isSome

def exported {State : Type*} (halt : Bool) : SimulatorQueryLoading.Control State → Control State
  | .admitting state machine trace request => .admitting state machine trace request
  | .executing frame => .running (.exporting frame
      (if halt then .returned (match frame.control with
        | .running machine => SimulatorDispatchQueryLoading.headBits machine.outputTape
        | _ => [])
      else .reversing [] (match frame.control with
        | .running machine => SimulatorDispatchQueryLoading.headBits machine.outputTape
        | _ => [])))

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  SimulatorDispatchQueryLoading.steps query table + 2 * n + 5

theorem running_run {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (fuel : Nat) (component : NativePacketComponent.Control State) :
    TimedExecution.eval (step n κ oracle) fuel (.running component) =
      (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) fuel component).map .running := by
  induction fuel generalizing component with
  | zero => simp [TimedExecution.eval, PMF.pure_map]
  | succ fuel ih => simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]

theorem ready_absorbing {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (control : Control State) (stopped : readyBoundary control = true) :
    step n κ oracle control = PMF.pure control := by
  cases control with
  | admitting => simp [readyBoundary, ready] at stopped
  | running component =>
      rw [step, NativePacketComponent.ready_absorbing (code n κ) oracle component stopped, PMF.pure_map]

theorem native_first {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    runToBoundary (step n κ oracle) nativeBoundary (SimulatorDispatchQueryLoading.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (fun target => (embed target, SimulatorDispatchQueryLoading.steps query table)) := by
  rw [show (Control.admitting state machine trace (compressionPacket query ++ [false])) =
    embed (.admitting state machine trace (compressionPacket query ++ [false])) by rfl,
    runToBoundary_map (SimulatorDispatchQueryLoading.step n κ oracle) (step n κ oracle)
      SimulatorQueryLoading.boundary nativeBoundary embed (fun source => by cases source <;> rfl)
      (fun source active => by
        cases source with
        | admitting => simp [step, embed, SimulatorDispatchQueryLoading.step, SimulatorQueryLoading.step,
            SimulatorQueryLoading.loadingFrame, PMF.pure_map]
        | executing frame =>
            simp only [SimulatorQueryLoading.boundary] at active
            simp [step, embed, SimulatorDispatchQueryLoading.step, SimulatorQueryLoading.step,
              NativePacketComponent.step, active, PMF.map_comp, Function.comp_def]),
    SimulatorDispatchQueryLoading.native_first_full oracle state machine trace query table tableLayout positive,
    PMF.map_comp]
  rfl

/-- Every actual native endpoint exports the same value used by its updated
table. The exporter executes physical scans and reversal, retaining the frame. -/
theorem export_stage {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (target : SimulatorQueryLoading.Control State)
    (support : target ∈ (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
      (SimulatorDispatchQueryLoading.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) (halt : Bool) :
    TimedExecution.eval (step n κ oracle) (2 * n + 4 + halt.toNat) (embed target) =
      PMF.pure (exported halt target) := by
  obtain ⟨value, before, actual, rfl, halted, _, blank, output, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table tableLayout positive target support
  rw [embed, running_run]
  cases halt with
  | false =>
      simpa only [Bool.toNat_false, Nat.add_zero, Bits.length_toList, exported, NativeCode.frame,
        Bool.false_eq_true, ↓reduceIte, bits, PMF.pure_map] using
        congrArg (PMF.map Control.running)
          (NativePacketComponent.export_prefix_before_ready (code n κ) oracle state actual trace
            value.toList before [] blank halted output)
  | true =>
      simpa only [Bool.toNat_true, show 2 * n + 4 + 1 = 2 * n + 5 by omega,
        Bits.length_toList, exported, NativeCode.frame, ↓reduceIte, bits, PMF.pure_map] using
        congrArg (PMF.map Control.running)
          (NativePacketComponent.export_prefix_run (code n κ) oracle state actual trace
            value.toList before [] blank halted output)

/-- The composed controller executes loading, native code and physical
export without rebuilding a table or resetting a completed native frame. -/
theorem stage_run {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (step n κ oracle)
      (SimulatorDispatchQueryLoading.steps query table + (2 * n + 4 + halt.toNat))
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map (exported halt) := by
  rw [runToBoundary_law (step n κ oracle) nativeBoundary (SimulatorDispatchQueryLoading.steps query table)
    _ _ (by omega), native_first oracle state machine trace query table tableLayout positive,
    PMF.bind_map]
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext target support
  simpa only [Function.comp_def, Nat.add_sub_cancel_left] using
    export_stage oracle state machine trace query table tableLayout positive target support halt

theorem exported_ready {State : Type*} (halt : Bool) (frame : Configuration State) :
    readyBoundary (exported halt (.executing frame)) = halt := by
  cases halt <;> simp [readyBoundary, ready, exported, NativePacketComponent.ready]

theorem first_joint {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    runToBoundary (step n κ oracle) readyBoundary (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (fun target => (exported true target, steps query table)) := by
  have stage (halt : Bool) := stage_run oracle state machine trace query table tableLayout positive halt
  have boundaryAt (halt : Bool) : ∀ target ∈ (TimedExecution.eval (step n κ oracle)
      (SimulatorDispatchQueryLoading.steps query table + (2 * n + 4 + halt.toNat))
      (.admitting state machine trace (compressionPacket query ++ [false]))).support,
      readyBoundary target = halt := by
    intro target support
    rw [stage halt, PMF.mem_support_map_iff] at support
    obtain ⟨middle, supported, rfl⟩ := support
    obtain ⟨frame, _, rfl, _, _⟩ := SimulatorDispatchQueryLoading.native_returned oracle state machine trace
      query table tableLayout positive middle supported
    exact exported_ready halt frame
  have joint := runToBoundary_joint_of_adjacent (step n κ oracle) readyBoundary
    (.admitting state machine trace (compressionPacket query ++ [false]))
    (SimulatorDispatchQueryLoading.steps query table + (2 * n + 4)) (ready_absorbing n κ oracle)
    (by simpa only [Bool.toNat_false, Nat.add_zero] using boundaryAt false)
    (by simpa only [Bool.toNat_true, Nat.add_assoc] using boundaryAt true)
  have clock : SimulatorDispatchQueryLoading.steps query table + (2 * n + 4) + 1 = steps query table := by
    unfold steps
    omega
  rw [clock] at joint
  have completed : TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map (exported true) := by
    simpa only [Bool.toNat_true, ← clock, Nat.add_assoc] using stage true
  rw [completed, PMF.map_comp] at joint
  exact joint

def observation {State : Type*} (control : Control State) :
    Option (State × List (List Bool × List Bool) × Option (List Bool × List Bool)) :=
  match ready control with
  | none => none
  | some (frame, packet) => match frame.control with
    | .running machine => some (frame.state, frame.reverseTrace, some (machine.inputTape.bits, packet))
    | _ => none

theorem run {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map (exported true) := by
  simpa only [Bool.toNat_true, steps, Nat.add_assoc] using
    stage_run oracle state machine trace query table tableLayout positive true

/-- The observation uses the packet physically produced by the exporter.
It is not a mathematical decoding of the native output tape. -/
theorem response_correct_with_table {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n)
    (admissible : table.lookup query = none → terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map observation =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun output => some (output.1.2, trace, some (SimulatorLookup.tableBits output.1.1, output.2.toList))) := by
  rw [run oracle state machine trace query table tableLayout positive, PMF.map_comp]
  rw [← SimulatorDispatchQueryLoading.response_correct_with_table oracle ideal initial terminal state machine trace
    query table tableLayout positive admissible]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext target support
  obtain ⟨value, before, actual, rfl, _, _, _, _, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table tableLayout positive target support
  rfl

/-- Every returned actual machine retains the complete table at its head.
It can therefore be admitted directly for the next raw request. -/
theorem returned_layout {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (target : Control State)
    (support : target ∈ (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ (value : Bits n) (actual : Machine.Configuration),
      target = .running (.exporting (NativeCode.frame state trace actual) (.returned value.toList)) ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup query).isSome then table else (query, value) :: table))) := by
  rw [run oracle state machine trace query table tableLayout positive, PMF.mem_support_map_iff] at support
  obtain ⟨middle, supported, rfl⟩ := support
  obtain ⟨value, before, actual, rfl, _, input, _, _, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table tableLayout positive middle supported
  refine ⟨value, actual, ?_, input⟩
  simp only [exported, NativeCode.frame, ↓reduceIte, bits]

theorem steps_le {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (positive : 0 < n) :
    steps query table ≤ table.length * (15 * n + 12 * κ + 26) + 21 * n + 12 * κ + 40 := by
  have bound := SimulatorDispatchQueryLoading.steps_le query table positive
  unfold steps
  omega

end Foundation.Hash.Native.SimulatorQueryPacket
