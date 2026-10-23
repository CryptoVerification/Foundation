import Foundation.Constructions.Hash.NativeCompactMACPacket
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceOperational

/-! The compact MAC request is serviced without changing the caller code.
The native cache frame is retained, its exported response is physically
loaded into the caller, and the same caller is released for continuation.
This is a single service contract, not yet the whole four-call MAC run. -/
namespace Foundation.Hash.Native.CompactMACService
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

variable {State Source : Type}

def read : CompactMACPacket.Control State → Configuration State × List Bool
  | .admitting state machine trace _ => (NativeCode.frame state trace machine, [])
  | .running component => NativePacketComponent.read component

def beginRound (saved : Configuration State) (request : List Bool) : CompactMACPacket.Control State :=
  .admitting saved.state (SimulatorQueryService.retainedMachine saved.control) saved.reverseTrace request

variable (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (message : Message) (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))

noncomputable def packet : Procedure (CompactMACPacket.step oracle) Unit (Configuration State × List Bool) :=
  (CompactMACPacket.whole oracle state machine trace message table layout).observe read
    (fun _ output => .running (.exporting output.1 (.returned output.2))) (by
      intro _ output hs
      obtain ⟨value, actual, rfl, _, _⟩ := CompactMACPacket.whole_retained oracle state machine trace message table layout output hs
      rfl)

theorem packet_semantics :
    (packet oracle state machine trace message table layout).semantics () =
      ((CompactMACPacket.core oracle state machine trace message table).semantics ()).map SimulatorQueryService.exitRead := by
  change ((CompactMACPacket.whole oracle state machine trace message table layout).semantics ()).map read = _
  rw [CompactMACPacket.whole_semantics, PMF.map_comp]
  congr 1
  funext control
  cases control <;> rfl

/-- This comparison is semantic: only the new component consumes the compact
request at runtime. The reference uses the verified wide interface. -/
theorem packet_reference :
    (packet oracle state machine trace message table layout).semantics () =
      (SimulatorQueryService.simulatorPacketProcedure oracle table state machine trace (Backend.key message) layout
        (by decide)).semantics () := by
  rw [packet_semantics]
  change (TimedExecution.eval (CompactMACQuery.step oracle) (CompactMACQuery.steps message table)
    (.admitting state machine trace (encodeMessage message))).map SimulatorQueryService.exitRead = _
  rw [CompactMACQuery.native_run oracle state machine trace message table layout]
  rfl

theorem packet_width (output : Configuration State × List Bool)
    (supported : output ∈ ((packet oracle state machine trace message table layout).semantics ()).support) :
    output.2.length = 8 := by
  change output ∈ (((CompactMACPacket.whole oracle state machine trace message table layout).semantics ()).map read).support at supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨control, hc, rfl⟩ := supported
  obtain ⟨value, actual, rfl, _, _⟩ := CompactMACPacket.whole_retained oracle state machine trace message table layout control hc
  exact Bits.length_toList value

noncomputable def handler : PacketResponseService.Handler (CompactMACPacket.step oracle) CompactMACPacket.ready where
  execution := packet oracle state machine trace message table layout
  ready_exit := fun _ => rfl
  read := read
  read_exit := fun _ => rfl
  responseCap := 8
  response_bound := fun output hs => le_of_eq (packet_width oracle state machine trace message table layout output hs)

variable (callerCode : Code) (callerOracle : BitOracle Source) (caller : Machine.Configuration)
    (callerState : Source) (callerTrace : List (List Bool × List Bool))

noncomputable def service := PacketResponseService.service (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready
  (CompactMACPacket.ready_absorbing oracle) callerCode callerOracle caller callerState callerTrace (encodeMessage message)
  (handler oracle state machine trace message table layout)

theorem service_budget :
    (service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).budget () =
      CompactMACQuery.steps message table + 49 := by
  change (CompactMACQuery.steps message table + 21) + (3 * 8 + 4) = _
  omega

theorem service_steps_budget (entries : Nat) (size : table.length ≤ entries) :
    (service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).budget () ≤
      146 * entries + 244 := by
  rw [service_budget]
  have bound := CompactMACQuery.steps_budget message table entries size
  omega

theorem service_semantics :
    (service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).semantics () =
      ((packet oracle state machine trace message table layout).semantics ()).map
        (fun output => (output.1, NativeCallback.resumed caller callerState callerTrace (encodeMessage message) output.2)) :=
  PacketResponseService.service_semantics _ _ _ _ _ _ _ _ _ _ _

theorem service_reference :
    (service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).semantics () =
      (SimulatorQueryService.simulatorService oracle table state machine trace (Backend.key message) layout
        (by decide) callerCode callerOracle caller callerState callerTrace (encodeMessage message)).semantics () := by
  rw [service_semantics, packet_reference, SimulatorQueryService.simulatorService,
    PacketResponseService.service_semantics]
  rfl

/-- The actual updated cache and resumed caller follow lazy random-function
semantics. Both cache hits and fresh eight-bit sampling are included. -/
theorem service_lazy :
    ((service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).semantics ()).map
      (fun output => (SimulatorDispatchQueryLoading.view output.1, output.2)) =
    (RandomOracle.oracle table (Backend.key message)).map (fun answer =>
      ((state, trace, some (SimulatorLookup.tableBits answer.1, answer.2.toList)),
        NativeCallback.resumed caller callerState callerTrace (encodeMessage message) answer.2.toList)) := by
  rw [service_reference]
  let retained : SimulatorQueryRound.Retained 8 0 State := {
    table := table
    saved := NativeCode.frame state trace machine
    machine := machine
    hControl := rfl
    tableLayout := layout }
  exact NativeOracleExecution.service_lazy oracle (by decide) callerCode callerOracle retained
    (Backend.key message) caller callerState callerTrace (encodeMessage message)

/-- The complete physical cache can be reused on the next call, and the
caller receives the packet actually produced by the exporter. -/
theorem service_retained (output : Configuration State × Configuration Source)
    (supported : output ∈ ((service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).semantics ()).support) :
    ∃ (value : Bits 8) (actual : Machine.Configuration),
      output.1 = NativeCode.frame state trace actual ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup (Backend.key message)).isSome then table else (Backend.key message, value) :: table))) ∧
      output.2 = NativeCallback.resumed caller callerState callerTrace (encodeMessage message) value.toList := by
  rw [service_semantics, PMF.mem_support_map_iff] at supported
  obtain ⟨packetOutput, hp, rfl⟩ := supported
  change packetOutput ∈ (((CompactMACPacket.whole oracle state machine trace message table layout).semantics ()).map read).support at hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨control, hc, rfl⟩ := hp
  obtain ⟨value, actual, rfl, _, input⟩ := CompactMACPacket.whole_retained oracle state machine trace message table layout control hc
  exact ⟨value, actual, rfl, input, rfl⟩

theorem service_operational : Procedure.Operational
    (service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace) := by
  apply PacketResponseService.service_operational

/-- Continue after the actual service time in the same source controller. -/
theorem service_law (horizon : Nat) (enough : CompactMACQuery.steps message table + 49 ≤ horizon) :
    TimedExecution.eval (PacketResponseSource.step (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready callerCode callerOracle)
      horizon (.processing caller callerState callerTrace (encodeMessage message)
        (.admitting state machine trace (encodeMessage message))) =
      ((service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).costed ()).bind
        (fun result => TimedExecution.eval
          (PacketResponseSource.step (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready callerCode callerOracle)
          (horizon - result.2) (.source result.1.1 result.1.2)) := by
  exact PacketResponseService.service_law (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready
    (CompactMACPacket.ready_absorbing oracle) callerCode callerOracle caller callerState callerTrace (encodeMessage message)
    (handler oracle state machine trace message table layout) horizon (by
      change (CompactMACQuery.steps message table + 21) + (3 * 8 + 4) ≤ horizon
      omega)

/-- Admission from the awaiting caller is one additional ownership step. -/
theorem awaiting_law (horizon : Nat) (enough : CompactMACQuery.steps message table + 49 ≤ horizon) :
    TimedExecution.eval (PacketResponseSource.step (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready callerCode callerOracle)
      (horizon + 1) (.source (NativeCode.frame state trace machine)
        ⟨callerState, .awaiting caller (encodeMessage message), callerTrace⟩) =
      ((service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).costed ()).bind
        (fun result => TimedExecution.eval
          (PacketResponseSource.step (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready callerCode callerOracle)
          (horizon - result.2) (.source result.1.1 result.1.2)) := by
  rw [TimedExecution.eval]
  simp only [PacketResponseSource.step, PMF.pure_bind]
  exact service_law oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace horizon enough

/-- The reported return time is reachable, bounded, and correlated with the
actual retained native cache and the complete resumed caller frame. -/
theorem service_costed (result : (Configuration State × Configuration Source) × Nat)
    (supported : result ∈ ((service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace).costed ()).support)
    (entries : Nat) (size : table.length ≤ entries) :
    PacketResponseSource.Control.source result.1.1 result.1.2 ∈
      (TimedExecution.eval
        (PacketResponseSource.step (CompactMACPacket.step oracle) beginRound CompactMACPacket.ready callerCode callerOracle)
        result.2 (.processing caller callerState callerTrace (encodeMessage message)
          (.admitting state machine trace (encodeMessage message)))).support ∧
    result.2 ≤ 146 * entries + 244 ∧
    ∃ (value : Bits 8) (actual : Machine.Configuration),
      result.1.1 = NativeCode.frame state trace actual ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup (Backend.key message)).isSome then table else (Backend.key message, value) :: table))) ∧
      result.1.2 = NativeCallback.resumed caller callerState callerTrace (encodeMessage message) value.toList := by
  let execution := service oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace
  exact ⟨service_operational oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace () result supported,
    (execution.bounded () result supported).trans
      (service_steps_budget oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace entries size),
    service_retained oracle state machine trace message table layout callerCode callerOracle caller callerState callerTrace result.1
      (execution.result_support () result supported)⟩

end Foundation.Hash.Native.CompactMACService
