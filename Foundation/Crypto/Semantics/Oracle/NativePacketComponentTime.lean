import Foundation.Crypto.Semantics.Oracle.NativePacketComponent
import Foundation.Crypto.Semantics.Machine.CellResponseExportExactTime

/-! First physical packet return for a completed native oracle component.
The completed frame remains retained, including all private state/history. -/
namespace CryptoOracle.Interactive.NativePacketComponent
open Foundation.Probability TimedExecution Machine
universe u
set_option backward.isDefEq.respectTransparency false

def readyBoundary {State : Type u} (control : Control State) : Bool := (ready control).isSome

/-- The explicit return transition is still pending at the adjacent horizon. -/
theorem export_cells_before_ready {State : Type u} (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (packet : List Bool) (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseLoading.loaded packet)) :
    TimedExecution.eval (step code oracle) (2 * packet.length + 4)
      (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.reversing [] packet)) := by
  rw [show 2 * packet.length + 4 = 1 + (2 * packet.length + 3) by omega, eval_add]
  have first : TimedExecution.eval (step code oracle) 1 (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.running machine)) := by
    simp [TimedExecution.eval, step, Reification.terminal, halted]
  rw [first, PMF.pure_bind, exporting_run,
    Machine.CellResponseExport.run_fromHead_before_return [] machine packet halted layout, PMF.pure_map]

/-- Ownership transfer plus scan/reversal has the exact first-return cost,
not an absorbing analysis horizon. Empty packets are included. -/
theorem export_cells_first_joint {State : Type u} (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (packet : List Bool) (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseLoading.loaded packet)) :
    runToBoundary (step code oracle) readyBoundary (2 * packet.length + 5)
      (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.returned packet), 2 * packet.length + 5) := by
  have before := export_cells_before_ready code oracle state machine trace packet halted layout
  have after := export_cells_run code oracle state machine trace packet halted layout
  have joint := runToBoundary_joint_of_adjacent (step code oracle) readyBoundary
    (.computing ⟨state, .running machine, trace⟩) (2 * packet.length + 4)
    (ready_absorbing code oracle)
    (by intro control hc; rw [before] at hc
        have he : control = .exporting ⟨state, .running machine, trace⟩ (.reversing [] packet) := by simpa using hc
        rw [he]; rfl)
    (by intro control hc; rw [show 2 * packet.length + 4 + 1 = 2 * packet.length + 5 by omega, after] at hc
        have he : control = .exporting ⟨state, .running machine, trace⟩ (.returned packet) := by simpa using hc
        rw [he]; rfl)
  simpa only [show 2 * packet.length + 4 + 1 = 2 * packet.length + 5 by omega,
    after, PMF.pure_map] using joint

end CryptoOracle.Interactive.NativePacketComponent
