import Foundation.Crypto.Semantics.Machine.NativeBitSampler
import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentTime
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Local fair-bit generation and physical packet export with a constant
six-instruction native program. No oracle capability is invoked, and every
private-state/history prefix is retained. The width-marker tape is supplied
at entry; allocation of that tape is outside this component's cost. -/
namespace CryptoOracle.Interactive.NativeUniformPacket
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev code : Code := NativeCode.code Machine.OneTimePad.keygen

@[simp] theorem code_length : code.length = 6 := rfl

/-- The local sampler has no capability invocation in any instruction. -/
theorem code_no_calls : Instruction.call ∉ code := by
  simp [code, NativeCode.code, Machine.OneTimePad.keygen]

def start {State : Type*} (width : Nat) (state : State)
    (prior : List (List Bool × List Bool)) : Configuration State :=
  NativeCode.frame state prior (Machine.OneTimePad.state [] [] (List.replicate width true))

def finish {State : Type*} {width : Nat} (state : State)
    (prior : List (List Bool × List Bool)) (bits : Bits width) : Configuration State :=
  NativeCode.frame state prior (Machine.OneTimePad.finish 5 (List.replicate width true) bits.toList)

variable {State : Type*} (oracle : BitOracle State) (width : Nat) (state : State)
    (prior : List (List Bool × List Bool))

theorem native_run :
    TimedExecution.eval (Reification.timedStep code oracle) (5 * width + 2)
      (start width state prior) = (uniform (Bits width)).map (finish state prior) := by
  rw [start, NativeCode.closed_eval _ oracle NativeBitSampler.closed _ _ _ _ (Or.inr (by change 0 < 6; decide)),
    Machine.OneTimePad.keygen_typed_run]
  simp only [List.nil_append, PMF.map_comp, Function.comp_def]
  rfl

theorem native_before_halt :
    TimedExecution.eval (Reification.timedStep code oracle) (5 * width + 1)
      (start width state prior) = (uniform (Bits width)).map (fun bits =>
        NativeCode.frame state prior
          { Machine.OneTimePad.finish 5 (List.replicate width true) bits.toList with halted := false }) := by
  rw [start, NativeCode.closed_eval _ oracle NativeBitSampler.closed _ _ _ _ (Or.inr (by change 0 < 6; decide)),
    NativeBitSampler.before_halt]
  simp only [List.nil_append, PMF.map_comp, Function.comp_def]

theorem native_first_joint :
    runToBoundary (Reification.timedStep code oracle) (fun frame => Reification.terminal frame.control)
      (5 * width + 2) (start width state prior) =
    (uniform (Bits width)).map (fun bits => (finish state prior bits, 5 * width + 2)) := by
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep code oracle)
    (fun frame => Reification.terminal frame.control) (start width state prior) (5 * width + 1)
    (by intro frame halted; simp [Reification.timedStep, halted])
    (by intro frame support
        rw [native_before_halt oracle width state prior, PMF.mem_support_map_iff] at support
        obtain ⟨bits, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [show 5 * width + 1 + 1 = 5 * width + 2 by omega,
          native_run oracle width state prior, PMF.mem_support_map_iff] at support
        obtain ⟨bits, _, rfl⟩ := support
        rfl)
  simpa only [show 5 * width + 1 + 1 = 5 * width + 2 by omega,
    native_run oracle width state prior, PMF.map_comp, Function.comp_def] using h

theorem component_first_joint :
    runToBoundary (NativePacketComponent.step code oracle) NativePacketComponent.boundary
      (5 * width + 2) (.computing (start width state prior)) =
    (uniform (Bits width)).map (fun bits =>
      (.computing (finish state prior bits), 5 * width + 2)) := by
  rw [runToBoundary_map (Reification.timedStep code oracle) (NativePacketComponent.step code oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]),
    native_first_joint oracle width state prior, PMF.map_comp]
  rfl

/-- Export from the sampler's actual end-of-output tape, charging the rewind
as well as collection/reversal. The retained full native frame is unchanged. -/
theorem export_run (bits : Bits width) :
    TimedExecution.eval (NativePacketComponent.step code oracle) (3 * width + 5)
      (.computing (finish state prior bits)) =
    PMF.pure (.exporting (finish state prior bits) (.returned bits.toList)) := by
  rw [show 3 * width + 5 = 1 + (3 * width + 4) by omega, eval_add]
  have first : TimedExecution.eval (NativePacketComponent.step code oracle) 1
      (.computing (finish state prior bits)) =
      PMF.pure (.exporting (finish state prior bits)
        (.running (Machine.OneTimePad.finish 5 (List.replicate width true) bits.toList))) := by
    simp [TimedExecution.eval, NativePacketComponent.step, finish, NativeCode.frame, Reification.terminal,
      Machine.OneTimePad.finish]
  rw [first, PMF.pure_bind, NativePacketComponent.exporting_run]
  rw [show 3 * width + 4 = 3 * bits.toList.length + 4 by simp]
  rw [Machine.CellResponseExport.run [] _ bits.toList rfl (Tape.Equivalent.refl _), PMF.pure_map]

theorem export_before_return (bits : Bits width) :
    TimedExecution.eval (NativePacketComponent.step code oracle) (3 * width + 4)
      (.computing (finish state prior bits)) =
    PMF.pure (.exporting (finish state prior bits) (.reversing [] bits.toList)) := by
  rw [show 3 * width + 4 = 1 + (3 * width + 3) by omega, eval_add]
  have first : TimedExecution.eval (NativePacketComponent.step code oracle) 1
      (.computing (finish state prior bits)) =
      PMF.pure (.exporting (finish state prior bits)
        (.running (Machine.OneTimePad.finish 5 (List.replicate width true) bits.toList))) := by
    simp [TimedExecution.eval, NativePacketComponent.step, finish, NativeCode.frame, Reification.terminal,
      Machine.OneTimePad.finish]
  rw [first, PMF.pure_bind, NativePacketComponent.exporting_run]
  rw [show 3 * width + 3 = 3 * bits.toList.length + 3 by simp]
  rw [Machine.CellResponseExport.run_before_return [] _ bits.toList rfl (Tape.Equivalent.refl _), PMF.pure_map]

theorem packet_run :
    TimedExecution.eval (NativePacketComponent.step code oracle) (8 * width + 7)
      (.computing (start width state prior)) =
    (uniform (Bits width)).map (fun bits =>
      .exporting (finish state prior bits) (.returned bits.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step code oracle) NativePacketComponent.boundary
    (5 * width + 2) _ _ (by omega), component_first_joint oracle width state prior, PMF.bind_map]
  simp only [Function.comp_def, show 8 * width + 7 - (5 * width + 2) = 3 * width + 5 by omega,
    export_run oracle width state prior]
  rfl

theorem packet_before_return :
    TimedExecution.eval (NativePacketComponent.step code oracle) (8 * width + 6)
      (.computing (start width state prior)) =
    (uniform (Bits width)).map (fun bits =>
      .exporting (finish state prior bits) (.reversing [] bits.toList)) := by
  rw [runToBoundary_law (NativePacketComponent.step code oracle) NativePacketComponent.boundary
    (5 * width + 2) _ _ (by omega), component_first_joint oracle width state prior, PMF.bind_map]
  simp only [Function.comp_def, show 8 * width + 6 - (5 * width + 2) = 3 * width + 4 by omega,
    export_before_return oracle width state prior]
  rfl

/-- Exact first physical packet return, not a padded analysis horizon. -/
theorem packet_first_joint :
    runToBoundary (NativePacketComponent.step code oracle) NativePacketComponent.readyBoundary
      (8 * width + 7) (.computing (start width state prior)) =
    (uniform (Bits width)).map (fun bits =>
      (.exporting (finish state prior bits) (.returned bits.toList), 8 * width + 7)) := by
  have h := runToBoundary_joint_of_adjacent (NativePacketComponent.step code oracle)
    NativePacketComponent.readyBoundary (.computing (start width state prior)) (8 * width + 6)
    (NativePacketComponent.ready_absorbing code oracle)
    (by intro control support
        rw [packet_before_return oracle width state prior, PMF.mem_support_map_iff] at support
        obtain ⟨bits, _, rfl⟩ := support
        rfl)
    (by intro control support
        rw [show 8 * width + 6 + 1 = 8 * width + 7 by omega,
          packet_run oracle width state prior, PMF.mem_support_map_iff] at support
        obtain ⟨bits, _, rfl⟩ := support
        rfl)
  simpa only [show 8 * width + 6 + 1 = 8 * width + 7 by omega,
    packet_run oracle width state prior, PMF.map_comp, Function.comp_def] using h

/-- Reuse the existing packet-service contract with the actual returned
native frame and packet. The logical observer never constructs the packet. -/
noncomputable def procedure :
    Procedure (NativePacketComponent.step code oracle) Unit (Configuration State × List Bool) :=
  Procedure.ofFixed _
    (fun _ => .computing (start width state prior))
    (fun _ output => .exporting output.1 (.returned output.2))
    (fun _ => (uniform (Bits width)).map (fun bits => (finish state prior bits, bits.toList)))
    (fun _ => 8 * width + 7)
    (fun _ => by rw [packet_run oracle width state prior, PMF.map_comp]; rfl)

theorem procedure_operational : Procedure.Operational (procedure oracle width state prior) := by
  apply Procedure.operational_ofFixed

noncomputable def handler :
    PacketResponseService.Handler (NativePacketComponent.step code oracle) NativePacketComponent.ready where
  execution := procedure oracle width state prior
  ready_exit _ := rfl
  read := NativePacketComponent.read
  read_exit _ := rfl
  responseCap := width
  response_bound := by
    intro output support
    change output ∈ ((uniform (Bits width)).map _).support at support
    rw [PMF.mem_support_map_iff] at support
    obtain ⟨bits, _, rfl⟩ := support
    simp

theorem handler_exact : (handler oracle width state prior).ExactFirstReady := by
  change (runToBoundary _ NativePacketComponent.readyBoundary (8 * width + 7)
    (.computing (start width state prior))).map
      (fun result => (NativePacketComponent.read result.1, result.2)) = _
  rw [packet_first_joint oracle width state prior, PMF.map_comp]
  simp only [handler, procedure, TimedExecution.Procedure.ofFixed, PMF.map_comp,
    Function.comp_def, NativePacketComponent.read]

end CryptoOracle.Interactive.NativeUniformPacket
