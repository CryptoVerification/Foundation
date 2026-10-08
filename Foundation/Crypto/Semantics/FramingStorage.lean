import Foundation.Crypto.Semantics.Framing
import Foundation.Crypto.Semantics.ResourceGrowth

/-! Retained caller data is charged as part of physical component storage.
Framing does not allocate the frame; it is an explicit entry precondition. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth
universe u v
variable {State : Type u} {Saved : Type v}

def framedSize (size : State → Nat) (savedSize : Saved → Nat) (frame : State × Saved) : Nat :=
  size frame.1 + savedSize frame.2

/-- A local component bound survives retaining arbitrary tapes, private keys,
external states, and histories measured by the supplied saved-size function. -/
theorem framed_local (step : State → PMF State) (size : State → Nat)
    (savedSize : Saved → Nat) (increment : Nat)
    (localBound : ∀ start next, next ∈ (step start).support → size next ≤ size start + increment)
    (start next : State × Saved) (h : next ∈ (framedStep step start).support) :
    framedSize size savedSize next ≤ framedSize size savedSize start + increment := by
  rw [framedStep, PMF.mem_support_map_iff] at h
  obtain ⟨value, hv, he⟩ := h
  subst next
  have hb := localBound start.1 value hv
  simp only [framedSize]
  omega

theorem framed_peak (step : State → PMF State) (size : State → Nat)
    (savedSize : Saved → Nat) (increment : Nat)
    (localBound : ∀ start next, next ∈ (step start).support → size next ≤ size start + increment)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start intermediate : State × Saved)
    (h : intermediate ∈ (eval (framedStep step) elapsed start).support) :
    framedSize size savedSize intermediate ≤ framedSize size savedSize start + horizon * increment :=
  prefix_bound (framedStep step) (framedSize size savedSize) increment
    (framed_local step size savedSize increment localBound) horizon elapsed hElapsed start intermediate h

end Foundation.Probability.TimedExecution.ResourceGrowth
