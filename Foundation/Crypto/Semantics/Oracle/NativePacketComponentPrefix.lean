import Foundation.Crypto.Semantics.Oracle.NativePacketComponentTime

/-! The existing packet exporter needs only the adjacent left blank.
Arbitrary older private output cells beyond that blank are retained. -/
namespace CryptoOracle.Interactive.NativePacketComponent
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem export_prefix_run {State : Type*} (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (packet : List Bool) (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent
      { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    TimedExecution.eval (step code oracle) (2 * packet.length + 5)
      (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.returned packet)) := by
  rw [show 2 * packet.length + 5 = 1 + (2 * packet.length + 4) by omega, eval_add]
  have first : TimedExecution.eval (step code oracle) 1 (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.running machine)) := by
    simp [TimedExecution.eval, step, Reification.terminal, halted]
  rw [first, PMF.pure_bind, exporting_run,
    CellResponseExport.run_fromHead_withPrefix [] machine packet before tail blank halted layout, PMF.pure_map]

theorem export_prefix_before_ready {State : Type*} (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (packet : List Bool) (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent
      { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    TimedExecution.eval (step code oracle) (2 * packet.length + 4)
      (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.reversing [] packet)) := by
  rw [show 2 * packet.length + 4 = 1 + (2 * packet.length + 3) by omega, eval_add]
  have first : TimedExecution.eval (step code oracle) 1 (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.running machine)) := by
    simp [TimedExecution.eval, step, Reification.terminal, halted]
  rw [first, PMF.pure_bind, exporting_run,
    CellResponseExport.run_fromHead_withPrefix_before_return [] machine packet before tail blank halted layout, PMF.pure_map]

theorem export_prefix_first_joint {State : Type*} (code : Code) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (packet : List Bool) (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent
      { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    runToBoundary (step code oracle) readyBoundary (2 * packet.length + 5)
      (.computing ⟨state, .running machine, trace⟩) =
      PMF.pure (.exporting ⟨state, .running machine, trace⟩ (.returned packet), 2 * packet.length + 5) := by
  have beforeRun := export_prefix_before_ready code oracle state machine trace packet before tail blank halted layout
  have afterRun := export_prefix_run code oracle state machine trace packet before tail blank halted layout
  have h := runToBoundary_joint_of_adjacent (step code oracle) readyBoundary
    (.computing ⟨state, .running machine, trace⟩) (2 * packet.length + 4)
    (ready_absorbing code oracle)
    (by intro control support; rw [beforeRun, PMF.mem_support_pure_iff] at support; subst control; rfl)
    (by intro control support
        rw [show 2 * packet.length + 4 + 1 = 2 * packet.length + 5 by omega,
          afterRun, PMF.mem_support_pure_iff] at support
        subst control; rfl)
  simpa only [show 2 * packet.length + 4 + 1 = 2 * packet.length + 5 by omega,
    afterRun, PMF.pure_map] using h

end CryptoOracle.Interactive.NativePacketComponent
