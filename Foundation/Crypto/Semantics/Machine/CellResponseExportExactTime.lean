import Foundation.Crypto.Semantics.Machine.CellResponseExport
import Foundation.Crypto.Semantics.BoundaryExactTime
import Foundation.Crypto.Semantics.BoundaryStability

/-! Actual first-return time for cell-aware physical packet export.
The certificate horizon is exact, including for empty packets and inputs
with arbitrary cell-equivalent outer blank padding. -/
namespace Machine.CellResponseExport
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def returned : Control → Bool
  | .returned _ => true
  | _ => false

theorem returned_absorbing (code : Program) (control : Control)
    (h : returned control = true) : step code control = PMF.pure control := by
  cases control <;> simp_all [returned, step]

/-- The joint law records the first return, rather than a padded exit time. -/
theorem first_return_joint (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true)
    (hTape : machine.outputTape.Equivalent (ResponseExport.endTape packet)) :
    runToBoundary (step code) returned (3 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet, 3 * packet.length + 4) := by
  have hBefore := run_before_return code machine packet hHalt hTape
  have hAfter := run code machine packet hHalt hTape
  have hJoint := runToBoundary_joint_of_adjacent (step code) returned (.running machine)
    (3 * packet.length + 3) (returned_absorbing code)
    (by intro control hc; rw [hBefore] at hc
        have he : control = .reversing [] packet := by simpa using hc
        rw [he]; rfl)
    (by intro control hc; rw [show 3 * packet.length + 3 + 1 = 3 * packet.length + 4 by omega, hAfter] at hc
        have he : control = .returned packet := by simpa using hc
        rw [he]; rfl)
  simpa only [show 3 * packet.length + 3 + 1 = 3 * packet.length + 4 by omega,
    hAfter, PMF.pure_map] using hJoint

/-- Extra analysis fuel does not add absorbing padding to the recorded time. -/
theorem first_return_joint_of_le (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true)
    (hTape : machine.outputTape.Equivalent (ResponseExport.endTape packet))
    (fuel : Nat) (hFuel : 3 * packet.length + 4 ≤ fuel) :
    runToBoundary (step code) returned fuel (.running machine) =
      PMF.pure (.returned packet, 3 * packet.length + 4) := by
  have hJoint := first_return_joint code machine packet hHalt hTape
  rw [runToBoundary_fuel_stable (step code) returned (3 * packet.length + 4) fuel
    (.running machine) hFuel ?_, hJoint]
  intro result hr
  rw [hJoint] at hr
  have he : result = (.returned packet, 3 * packet.length + 4) := by simpa using hr
  rw [he]
  rfl

/-- With the head already at the first packet cell, all reversal steps have
finished one transition before the explicit return. Padding is retained. -/
theorem run_fromHead_withPrefix_before_return (code : Program) (machine : Configuration) (packet : List Bool)
    (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    eval (step code) (2 * packet.length + 3) (.running machine) =
      PMF.pure (.reversing [] packet) := by
  have left : machine.outputTape.left[0]?.getD none = none := (layout.2.1 0).trans blank
  rw [show 2 * packet.length + 3 = 1 + (1 + ((packet.length + 1) + packet.length)) by omega, eval_add]
  have first : eval (step code) 1 (.running machine) = PMF.pure (.rewinding machine.outputTape) := by
    simp [eval, step, halted]
  rw [first, PMF.pure_bind, eval_add]
  have rewound : eval (step code) 1 (.rewinding machine.outputTape) =
      PMF.pure (.collecting machine.outputTape []) := by simp [eval, step, left]
  rw [rewound, PMF.pure_bind, eval_add]
  have collected := collect_equivalent code packet [] tail before machine.outputTape layout
  simp only [List.append_nil] at collected
  rw [collected, PMF.pure_bind]
  simpa using reverse_before_return code packet.reverse []

theorem run_fromHead_before_return (code : Program) (machine : Configuration) (packet : List Bool)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseExport.fromCells (packet.map some ++ [none]))) :
    eval (step code) (2 * packet.length + 3) (.running machine) =
      PMF.pure (.reversing [] packet) := by
  exact run_fromHead_withPrefix_before_return code machine packet [] [] rfl halted layout

/-- Exact first physical return from a cell-equivalent head layout. -/
theorem first_return_fromHead_withPrefix_joint (code : Program) (machine : Configuration) (packet : List Bool)
    (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    runToBoundary (step code) returned (2 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet, 2 * packet.length + 4) := by
  have beforeRun := run_fromHead_withPrefix_before_return code machine packet before tail blank halted layout
  have after := run_fromHead_withPrefix code machine packet before tail blank halted layout
  have joint := runToBoundary_joint_of_adjacent (step code) returned (.running machine)
    (2 * packet.length + 3) (returned_absorbing code)
    (by intro control hc; rw [beforeRun] at hc
        have he : control = .reversing [] packet := by simpa using hc
        rw [he]; rfl)
    (by intro control hc; rw [show 2 * packet.length + 3 + 1 = 2 * packet.length + 4 by omega, after] at hc
        have he : control = .returned packet := by simpa using hc
        rw [he]; rfl)
  simpa only [show 2 * packet.length + 3 + 1 = 2 * packet.length + 4 by omega,
    after, PMF.pure_map] using joint
theorem first_return_fromHead_joint (code : Program) (machine : Configuration) (packet : List Bool)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseExport.fromCells (packet.map some ++ [none]))) :
    runToBoundary (step code) returned (2 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet, 2 * packet.length + 4) := by
  exact first_return_fromHead_withPrefix_joint code machine packet [] [] rfl halted layout

end Machine.CellResponseExport
