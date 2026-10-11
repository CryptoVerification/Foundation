import Foundation.Constructions.Hash.NativeSimulatorQueryPacket
import Foundation.Crypto.Semantics.Oracle.PacketResponseService
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceOperational

/-! One physical simulator round as the existing packet service: the private
compression table stays on the retained machine tape, the response is loaded
into the actual caller, and the updated frame is returned for the next
request. No query decoding or table reconstruction is executed at runtime. -/
namespace Foundation.Hash.Native.SimulatorQueryService
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The machine retained by a saved interactive frame. Only running frames
occur as component exits; other controls carry no usable machine. -/
def retainedMachine : Interactive.Control → Machine.Configuration
  | .running machine => machine
  | _ => {}

/-- Reading the retained frame and the already exported packet. Before the
component is ready this returns the admitted frame itself. -/
def read {State : Type*} : SimulatorQueryPacket.Control State → Configuration State × List Bool
  | .admitting state machine trace _request => (⟨state, .running machine, trace⟩, [])
  | .running component => NativePacketComponent.read component

/-- A new round starts at the retained frame's machine: the private table is
already at the head of its input tape. -/
def beginRound {State : Type*} (saved : Configuration State) (request : List Bool) :
    SimulatorQueryPacket.Control State :=
  .admitting saved.state (retainedMachine saved.control) saved.reverseTrace request

/-- Proof-side extraction of the retained frame and the packet from the
completed native frame; the exporter produced that packet physically. -/
def exitRead {State : Type*} : SimulatorQueryLoading.Control State → Configuration State × List Bool
  | .executing frame => (frame, match frame.control with
      | .running machine => SimulatorDispatchQueryLoading.headBits machine.outputTape
      | _ => [])
  | .admitting state machine trace _request => (⟨state, .running machine, trace⟩, [])

theorem exitRead_exported {State : Type*} (target : SimulatorQueryLoading.Control State) :
    read (SimulatorQueryPacket.exported true target) = exitRead target := by
  cases target with
  | admitting => rfl
  | executing frame => rfl

/-- The observation of the completed native frame, read from the retained
frame and the packet the exporter already produced. -/
def observationPair {State Source : Type*} (caller : Machine.Configuration) (callerState : Source)
    (trace : List (List Bool × List Bool)) (request : List Bool) (saved : Configuration State) :
    Option (State × List (List Bool × List Bool) × Option (List Bool × List Bool)) →
    (State × List (List Bool × List Bool) × Option (List Bool × List Bool)) × Configuration Source
  | some (a, b, some packet) =>
      ((a, b, some packet), NativeCallback.resumed caller callerState trace request packet.2)
  | _ => (SimulatorDispatchQueryLoading.view saved,
      NativeCallback.resumed caller callerState trace request [])

noncomputable def simulatorPacketProcedure {n κ : Nat} {State : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    Procedure (SimulatorQueryPacket.step n κ oracle) Unit (Configuration State × List Bool) :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => SimulatorQueryPacket.Control.admitting state machine trace
      (compressionPacket query ++ [false]))
    (fun _ output => SimulatorQueryPacket.Control.running
      (NativePacketComponent.Control.exporting output.1 (.returned output.2)))
    (fun _ => (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
        (SimulatorDispatchQueryLoading.steps query table)
        (SimulatorQueryLoading.Control.admitting state machine trace
          (compressionPacket query ++ [false]))).map exitRead)
    (fun _ => SimulatorQueryPacket.steps query table)
    (by
      intro input
      have completed := SimulatorQueryPacket.run oracle state machine trace query table tableLayout positive
      rw [completed, PMF.map_comp, PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind,
        ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext target supported
      obtain ⟨_, _, actual, rfl, _, _, _, _, _⟩ :=
        SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table tableLayout
          positive target supported
      rfl)

theorem simulatorPacketProcedure_costed {n κ : Nat} {State : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    (simulatorPacketProcedure oracle table state machine trace query tableLayout positive).costed () =
      (runToBoundary (SimulatorQueryPacket.step n κ oracle) SimulatorQueryPacket.readyBoundary
        (SimulatorQueryPacket.steps query table)
        (SimulatorQueryPacket.Control.admitting state machine trace
          (compressionPacket query ++ [false]))).map
        (fun result => (read result.1, result.2)) := by
  have joint := SimulatorQueryPacket.first_joint oracle state machine trace query table tableLayout positive
  unfold simulatorPacketProcedure
  simp only [TimedExecution.Procedure.ofFixed, PMF.map_comp]
  rw [joint, PMF.map_comp]
  congr 1
  funext target
  simp only [Function.comp_def]
  rw [exitRead_exported]

/-- The complete saved frame and packet are exactly those of the first
physical return; no absorbing padding state is returned. -/
noncomputable def simulatorPacketHandler {n κ : Nat} {State : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    PacketResponseService.Handler (SimulatorQueryPacket.step n κ oracle) SimulatorQueryPacket.ready where
  execution := simulatorPacketProcedure oracle table state machine trace query tableLayout positive
  ready_exit := fun _ => rfl
  read := read
  read_exit := by
    intro output
    rfl
  responseCap := n
  response_bound := by
    intro output support
    unfold simulatorPacketProcedure at support
    simp only [TimedExecution.Procedure.ofFixed] at support
    rw [PMF.mem_support_map_iff] at support
    obtain ⟨target, targetSupport, rfl⟩ := support
    obtain ⟨value, before, actual, rfl, halted, input, blank, outputEq, bits⟩ :=
      SimulatorDispatchQueryLoading.native_layout oracle state machine trace query table tableLayout
        positive target targetSupport
    simp only [exitRead, NativeCode.frame, bits, Bits.length_toList]
    exact Nat.le_refl _

theorem simulatorPacketHandler_exact {n κ : Nat} {State : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    (simulatorPacketHandler oracle table state machine trace query tableLayout positive).ExactFirstReady := by
  unfold PacketResponseService.Handler.ExactFirstReady
  have boundary : (fun control : SimulatorQueryPacket.Control State =>
      (SimulatorQueryPacket.ready control).isSome) = SimulatorQueryPacket.readyBoundary := rfl
  rw [boundary,
    show (simulatorPacketHandler oracle table state machine trace query tableLayout positive).execution
      = simulatorPacketProcedure oracle table state machine trace query tableLayout positive from rfl,
    show (simulatorPacketHandler oracle table state machine trace query tableLayout positive).read = read from rfl,
    simulatorPacketProcedure_costed]
  rfl

theorem simulatorPacketHandler_budget {n κ : Nat} {State : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    (simulatorPacketHandler oracle table state machine trace query tableLayout positive).execution.budget () =
      SimulatorQueryPacket.steps query table := by
  unfold simulatorPacketHandler simulatorPacketProcedure
  rfl

noncomputable def simulatorService {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :=
  PacketResponseService.service (SimulatorQueryPacket.step n κ oracle) beginRound
    SimulatorQueryPacket.ready (SimulatorQueryPacket.ready_absorbing n κ oracle) callerCode callerOracle
    caller callerState callerTrace request
    (simulatorPacketHandler oracle table state machine prior query tableLayout positive)

theorem simulatorService_entry {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    (simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
      caller callerState callerTrace request).entry () =
      PacketResponseSource.Control.processing caller callerState callerTrace request
        (beginRound ⟨state, .running machine, prior⟩ (compressionPacket query ++ [false])) := rfl

theorem simulatorService_budget {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    (simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
      caller callerState callerTrace request).budget () =
      SimulatorQueryPacket.steps query table + (3 * n + 4) := by
  rw [simulatorService, PacketResponseService.service_budget, simulatorPacketHandler_budget]
  rfl

theorem simulatorService_costed {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    (simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
      caller callerState callerTrace request).costed () =
      ((simulatorPacketProcedure oracle table state machine prior query tableLayout positive).costed ()).map
        (fun result => ((result.1.1, NativeCallback.resumed caller callerState callerTrace request result.1.2),
          result.2 + (3 * result.1.2.length + 4))) := by
  apply PacketResponseService.service_costed_of_exact
  exact simulatorPacketHandler_exact oracle table state machine prior query tableLayout positive

theorem simulatorService_operational {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) :
    Procedure.Operational
      (simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
        caller callerState callerTrace request) := by
  apply PacketResponseService.service_operational

/-- The actual resumed caller and the retained frame's private table follow
the fixed candidate simulator's distribution. The ideal state is unchanged
because this component makes no external oracle request. -/
theorem simulatorService_packet {n κ : Nat} {State Source : Type}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool)
    (ideal : Oracle (List (Bits κ)) (Bits n) State) (initial : Bits n) (terminal : Bits κ)
    (admissible : table.lookup query = none → terminalMessage initial terminal table query = none) :
    ((simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
      caller callerState callerTrace request).semantics ()).map
        (fun output => (SimulatorDispatchQueryLoading.view output.1, output.2)) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun answer : (CompressionTable (Bits κ) (Bits n) × State) × Bits n =>
          ((answer.1.2, prior, some (SimulatorLookup.tableBits answer.1.1, answer.2.toList)),
            NativeCallback.resumed caller callerState callerTrace request answer.2.toList)) := by
  have obs := SimulatorDispatchQueryLoading.response_correct_with_table oracle ideal initial terminal state
    machine prior query table tableLayout positive admissible
  rw [simulatorService, PacketResponseService.service_semantics, PMF.map_comp]
  have rhs : (compressionSimulator ideal initial terminal (table, state) query).map
      (fun answer : (CompressionTable (Bits κ) (Bits n) × State) × Bits n =>
        ((answer.1.2, prior, some (SimulatorLookup.tableBits answer.1.1, answer.2.toList)),
          NativeCallback.resumed caller callerState callerTrace request answer.2.toList)) =
    PMF.map (fun observed => observationPair caller callerState callerTrace request
      ⟨state, .running machine, prior⟩ observed)
      (PMF.map (SimulatorQueryLoading.observe (SimulatorDispatchQueryLoading.view))
        (TimedExecution.eval (SimulatorDispatchQueryLoading.step n κ oracle)
          (SimulatorDispatchQueryLoading.steps query table)
          (SimulatorQueryLoading.Control.admitting state machine prior
            (compressionPacket query ++ [false])))) := by
    rw [obs, PMF.map_comp]
    congr 1
  rw [rhs, simulatorPacketHandler]
  unfold simulatorPacketProcedure
  simp only [TimedExecution.Procedure.ofFixed]
  rw [PMF.map_comp, PMF.map_comp]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext target supported
  obtain ⟨value, before, actual, rfl, halted, input, blank, outputEq, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle state machine prior query table
      tableLayout positive target supported
  simp only [Function.comp_def, exitRead, SimulatorQueryLoading.observe,
    SimulatorDispatchQueryLoading.view, observationPair, NativeCode.frame]

/-- Every returned saved frame is running and carries the complete updated
private table at the head of its input tape, cell for cell. -/
theorem simulatorService_frame {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool)
    (output : Configuration State × Configuration Source)
    (hs : output ∈ ((simulatorService oracle table state machine prior query tableLayout positive
      callerCode callerOracle caller callerState callerTrace request).semantics ()).support) :
    ∃ (nextTable : CompressionTable (Bits κ) (Bits n)) (nextMachine : Machine.Configuration),
      output.1.control = .running nextMachine ∧
      nextMachine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits nextTable)) := by
  rw [simulatorService, PacketResponseService.service_semantics, PMF.mem_support_map_iff] at hs
  obtain ⟨saved, hos, rfl⟩ := hs
  have hos' : saved ∈ ((simulatorPacketHandler oracle table state machine prior query tableLayout
    positive).execution.semantics ()).support := hos
  unfold simulatorPacketHandler simulatorPacketProcedure at hos'
  simp only [TimedExecution.Procedure.ofFixed] at hos'
  rw [PMF.mem_support_map_iff] at hos'
  obtain ⟨target, htarget, rfl⟩ := hos'
  obtain ⟨value, before, actual, rfl, halted, input, blank, outputEq, bits⟩ :=
    SimulatorDispatchQueryLoading.native_layout oracle state machine prior query table tableLayout
      positive target htarget
  by_cases hHit : (table.lookup query).isSome = true
  · refine ⟨table, actual, rfl, ?_⟩
    simpa [hHit] using input
  · refine ⟨(query, value) :: table, actual, rfl, ?_⟩
    have hMiss : (table.lookup query).isSome = false := by
      cases h : table.lookup query <;> simp_all
    simpa [hMiss] using input

/-- Continue the same simulator component controller after the actual round
cost. The response boundary is not an absorbing end of the whole caller. -/
theorem simulatorService_law {n κ : Nat} {State Source : Type*}
    (oracle : BitOracle State) (table : CompressionTable (Bits κ) (Bits n)) (state : State)
    (machine : Machine.Configuration) (prior : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (callerCode : Code) (callerOracle : BitOracle Source)
    (caller : Machine.Configuration) (callerState : Source)
    (callerTrace : List (List Bool × List Bool)) (request : List Bool) (horizon : Nat)
    (enough : SimulatorQueryPacket.steps query table + (3 * n + 4) ≤ horizon) :
    TimedExecution.eval (PacketResponseSource.step (SimulatorQueryPacket.step n κ oracle) beginRound
      SimulatorQueryPacket.ready callerCode callerOracle) horizon
      (PacketResponseSource.Control.processing caller callerState callerTrace request
        (beginRound ⟨state, .running machine, prior⟩ (compressionPacket query ++ [false]))) =
    ((simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
      caller callerState callerTrace request).costed ()).bind
        (fun result => TimedExecution.eval (PacketResponseSource.step (SimulatorQueryPacket.step n κ oracle)
          beginRound SimulatorQueryPacket.ready callerCode callerOracle) (horizon - result.2)
          (PacketResponseSource.Control.source result.1.1 result.1.2)) := by
  have h := (simulatorService oracle table state machine prior query tableLayout positive callerCode callerOracle
    caller callerState callerTrace request).law () horizon (by rw [simulatorService_budget]; exact enough)
  have entry : (simulatorPacketProcedure oracle table state machine prior query tableLayout positive).entry ()
      = SimulatorQueryPacket.Control.admitting state machine prior (compressionPacket query ++ [false]) := rfl
  have beginEq : beginRound ⟨state, .running machine, prior⟩ (compressionPacket query ++ [false])
      = SimulatorQueryPacket.Control.admitting state machine prior (compressionPacket query ++ [false]) := rfl
  simp only [simulatorService, PacketResponseService.service_entry] at h
  rw [beginEq]
  exact h

end Foundation.Hash.Native.SimulatorQueryService
