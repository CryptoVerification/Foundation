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

end Machine.CellResponseExport
