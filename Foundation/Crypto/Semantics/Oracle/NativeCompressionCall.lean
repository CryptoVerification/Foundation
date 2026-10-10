import Foundation.Crypto.Semantics.Oracle.CallExecution
import Foundation.Crypto.Semantics.Oracle.NativePacketLaunch
import Foundation.Crypto.Semantics.Oracle.NativePacketComponentTime
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! A public compression request is loaded and executed by a fixed two
instruction program, then physically exported. No host-side response encoder
is used. The same oracle state may be retained from a preceding hash call. -/
namespace CryptoOracle.Interactive.NativeCompressionCall
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- One capability invocation followed by an ordinary native halt. -/
def code : Code := [.call, .native .halt]

def start {State : Type*} (state : State) (request : List Bool)
    (prior : List (List Bool × List Bool)) : Configuration State :=
  ⟨state, .running (NativePacketService.loaded request), prior⟩

def resumed {State : Type*} (request : List Bool) (prior : List (List Bool × List Bool))
    (answer : State × List Bool) : Configuration State :=
  ⟨answer.1, .running { pc := 1, outputTape := ResponseLoading.loaded answer.2 },
    (request, answer.2) :: prior⟩

def finish {State : Type*} (request : List Bool) (prior : List (List Bool × List Bool))
    (answer : State × List Bool) : Configuration State :=
  ⟨answer.1, .running { pc := 1, outputTape := ResponseLoading.loaded answer.2, halted := true },
    (request, answer.2) :: prior⟩

variable {State : Type*} (oracle : BitOracle State) (state : State) (request : List Bool)
    (prior : List (List Bool × List Bool)) (width : Nat)
    (hWidth : ∀ answer ∈ (oracle state request).support, answer.2.length = width)

include hWidth in
theorem call_run :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 3 * width + 6)
      (start state request prior) = (oracle state request).map (resumed request prior) := by
  exact CallExecution.run code oracle (NativePacketService.loaded request) state prior request width rfl rfl rfl hWidth

theorem finish_step (answer : State × List Bool) :
    Reification.timedStep code oracle (resumed request prior answer) =
      PMF.pure (finish request prior answer) := by
  simp [Reification.timedStep, Reification.terminal, Reification.perform,
    Reification.action, transition, code, resumed, finish, Machine.Instruction.next]

include hWidth in
theorem native_run :
    TimedExecution.eval (Reification.timedStep code oracle) (2 * request.length + 3 * width + 7)
      (start state request prior) = (oracle state request).map (finish request prior) := by
  rw [show 2 * request.length + 3 * width + 7 = (2 * request.length + 3 * width + 6) + 1 by omega,
    eval_add, call_run oracle state request prior width hWidth, PMF.bind_map]
  simp only [Function.comp_def, TimedExecution.eval, finish_step, PMF.pure_bind]
  rfl

include hWidth in
/-- The halt time is the first halt, not an analysis padding horizon. -/
theorem native_first_joint :
    runToBoundary (Reification.timedStep code oracle) (fun frame => Reification.terminal frame.control)
      (2 * request.length + 3 * width + 7) (start state request prior) =
    (oracle state request).map (fun answer =>
      (finish request prior answer, 2 * request.length + 3 * width + 7)) := by
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep code oracle)
    (fun frame => Reification.terminal frame.control) (start state request prior)
    (2 * request.length + 3 * width + 6)
    (by intro frame halted; simp [Reification.timedStep, halted])
    (by intro frame support
        rw [call_run oracle state request prior width hWidth, PMF.mem_support_map_iff] at support
        obtain ⟨answer, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [show 2 * request.length + 3 * width + 6 + 1 = 2 * request.length + 3 * width + 7 by omega,
          native_run oracle state request prior width hWidth, PMF.mem_support_map_iff] at support
        obtain ⟨answer, _, rfl⟩ := support
        rfl)
  simpa only [show 2 * request.length + 3 * width + 6 + 1 = 2 * request.length + 3 * width + 7 by omega,
    native_run oracle state request prior width hWidth, PMF.map_comp, Function.comp_def] using h

include hWidth in
/-- Stop at the same actual native halt inside the physical exporter. -/
theorem component_first_joint :
    runToBoundary (NativePacketComponent.step code oracle) NativePacketComponent.boundary
      (2 * request.length + 3 * width + 7) (.computing (start state request prior)) =
    (oracle state request).map (fun answer =>
      (.computing (finish request prior answer), 2 * request.length + 3 * width + 7)) := by
  rw [runToBoundary_map (Reification.timedStep code oracle) (NativePacketComponent.step code oracle)
    (fun frame => Reification.terminal frame.control) NativePacketComponent.boundary
    NativePacketComponent.Control.computing (fun _ => rfl)
    (fun frame active => by simp [NativePacketComponent.step, active]),
    native_first_joint oracle state request prior width hWidth, PMF.map_comp]
  rfl

include hWidth in
/-- Native call, actual halt and a physical read of the response. -/
theorem component_export_run :
    TimedExecution.eval (NativePacketComponent.step code oracle)
      ((2 * request.length + 3 * width + 7) + (2 * width + 5))
      (.computing (start state request prior)) =
    (oracle state request).map (fun answer =>
      .exporting (finish request prior answer) (.returned answer.2)) := by
  rw [runToBoundary_law (NativePacketComponent.step code oracle) NativePacketComponent.boundary
    (2 * request.length + 3 * width + 7) _ _ (by omega),
    component_first_joint oracle state request prior width hWidth, PMF.bind_map]
  simp only [Function.comp_def, Nat.add_sub_cancel_left]
  rw [← PMF.bindOnSupport_eq_bind, PMF.map, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext answer support
  have h := NativePacketComponent.export_run code oracle answer.1
    ({ pc := 1, outputTape := ResponseLoading.loaded answer.2, halted := true } : Machine.Configuration)
    ((request, answer.2) :: prior) answer.2 rfl rfl
  rw [hWidth answer support] at h
  exact h

include hWidth in
/-- The final physical return transition is still pending one step earlier. -/
theorem component_export_before_run :
    TimedExecution.eval (NativePacketComponent.step code oracle)
      ((2 * request.length + 3 * width + 7) + (2 * width + 4))
      (.computing (start state request prior)) =
    (oracle state request).map (fun answer =>
      .exporting (finish request prior answer) (.reversing [] answer.2)) := by
  rw [runToBoundary_law (NativePacketComponent.step code oracle) NativePacketComponent.boundary
    (2 * request.length + 3 * width + 7) _ _ (by omega),
    component_first_joint oracle state request prior width hWidth, PMF.bind_map]
  simp only [Function.comp_def, Nat.add_sub_cancel_left]
  rw [← PMF.bindOnSupport_eq_bind, PMF.map, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext answer support
  have h := NativePacketComponent.export_cells_before_ready code oracle answer.1
    ({ pc := 1, outputTape := ResponseLoading.loaded answer.2, halted := true } : Machine.Configuration)
    ((request, answer.2) :: prior) answer.2 rfl (Tape.Equivalent.refl _)
  rw [hWidth answer support] at h
  exact h

/-- Total raw loading plus native call/halt and physical response export. -/
def rawSteps (requestLength responseWidth : Nat) : Nat :=
  (3 * requestLength + 4) + (2 * requestLength + 3 * responseWidth + 7) + (2 * responseWidth + 5)

include hWidth in
/-- The loaded raw request is executed unchanged; the returned state and
packet are actual physical outputs of the existing launch controller. -/
theorem raw_export_run :
    TimedExecution.eval (NativePacketLaunch.step code oracle false prior) (rawSteps request.length width)
      (.preparing state (.loading request {})) =
    (oracle state request).map (fun answer =>
      .running (.exporting (finish request prior answer) (.returned answer.2))) := by
  rw [NativePacketLaunch.launch_continues code oracle state request
    (rawSteps request.length width) (by unfold rawSteps; omega) false prior]
  have entry : NativePacketLaunch.handoffFrame state (NativePacketService.loaded request) false prior =
      start state request prior := rfl
  rw [entry, NativePacketLaunch.running_eval]
  have budget : rawSteps request.length width - (3 * request.length + 4) =
      (2 * request.length + 3 * width + 7) + (2 * width + 5) := by unfold rawSteps; omega
  rw [budget, component_export_run oracle state request prior width hWidth, PMF.map_comp]
  rfl

include hWidth in
/-- Every actual branch remains outside packet readiness at the adjacent
horizon, including zero-width responses. -/
theorem raw_export_before_run :
    TimedExecution.eval (NativePacketLaunch.step code oracle false prior) (rawSteps request.length width - 1)
      (.preparing state (.loading request {})) =
    (oracle state request).map (fun answer =>
      .running (.exporting (finish request prior answer) (.reversing [] answer.2))) := by
  rw [NativePacketLaunch.launch_continues code oracle state request
    (rawSteps request.length width - 1) (by unfold rawSteps; omega) false prior]
  have entry : NativePacketLaunch.handoffFrame state (NativePacketService.loaded request) false prior =
      start state request prior := rfl
  rw [entry, NativePacketLaunch.running_eval]
  have budget : rawSteps request.length width - 1 - (3 * request.length + 4) =
      (2 * request.length + 3 * width + 7) + (2 * width + 4) := by unfold rawSteps; omega
  rw [budget, component_export_before_run oracle state request prior width hWidth, PMF.map_comp]
  rfl

end CryptoOracle.Interactive.NativeCompressionCall
