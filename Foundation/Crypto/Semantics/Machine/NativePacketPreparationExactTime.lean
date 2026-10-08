import Foundation.Crypto.Semantics.Machine.NativePacketService
import Foundation.Crypto.Semantics.BoundaryCountdown

/-! The raw request loader reaches its native handoff for the first time
at its certificate horizon. Every buffer write, movement and handoff is
charged, including empty requests. -/
namespace Machine.NativePacketService
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def preparedBoundary : Control → Bool
  | .executing _ => true
  | _ => false

def preparationRemaining : Control → Nat
  | .loading remaining tape => 3 * remaining.length + tape.left.length + 3
  | .advancing remaining tape => 3 * remaining.length + tape.left.length + 5
  | .rewinding tape => tape.left.length + 2
  | .prepared _ => 1
  | .executing _ => 0

theorem preparation_zero (control : Control) :
    preparedBoundary control = true ↔ preparationRemaining control = 0 := by
  cases control <;> simp [preparedBoundary, preparationRemaining]

theorem preparation_decreases (code : Program) (control : Control)
    (h : preparedBoundary control = false) (next : Control)
    (hn : next ∈ (step code control).support) :
    preparationRemaining next + 1 = preparationRemaining control := by
  cases control with
  | loading remaining tape =>
      cases remaining <;> simp only [step, PMF.mem_support_pure_iff] at hn <;>
        subst next <;> simp [preparationRemaining, Tape.write] <;> omega
  | advancing remaining tape =>
      simp only [step, PMF.mem_support_pure_iff] at hn
      subst next
      cases ht : tape.right <;> simp [preparationRemaining, Tape.moveRight, ht] <;> omega
  | rewinding tape =>
      cases ht : tape.left with
      | nil =>
          simp only [step, ht, PMF.mem_support_pure_iff] at hn
          subst next
          simp [preparationRemaining, ht]
      | cons cell rest =>
          simp only [step, ht, PMF.mem_support_pure_iff] at hn
          subst next
          simp [preparationRemaining, Tape.moveLeft, ht]
  | prepared machine =>
      simp only [step, PMF.mem_support_pure_iff] at hn
      subst next
      rfl
  | executing component => simp [preparedBoundary] at h

/-- Initial request length determines the actual first handoff time. -/
theorem preparation_first_joint (code : Program) (request : List Bool) :
    runToBoundary (step code) preparedBoundary (3 * request.length + 3) (.loading request {}) =
      PMF.pure (.executing (.running (loaded request)), 3 * request.length + 3) := by
  have h := runToBoundary_countdown_joint (step code) preparedBoundary preparationRemaining
    preparation_zero (preparation_decreases code) (.loading request {})
  simpa only [preparationRemaining, List.length_nil, Nat.add_zero, prepare_run,
    PMF.pure_map] using h

end Machine.NativePacketService
