import Foundation.Crypto.Semantics.ResourceGrowth

/-! Convert a slowly growing analysis measure into a bound on all retained
physical data. The monotone envelope can be reused with arbitrary machines,
resource measures and execution boundaries; it is not a memory allocator. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth
universe u
variable {State : Type u}

structure Envelope (step : State → PMF State) where
  extent : State → Nat
  retained : State → Nat
  bound : Nat → Nat
  monotone : Monotone bound
  covers : ∀ state, retained state ≤ bound (extent state)
  increment : Nat
  grows : ∀ start next, next ∈ (step start).support →
    extent next ≤ extent start + increment

namespace Envelope
variable {step : State → PMF State} (E : Envelope step)

theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : State) (h : intermediate ∈ (eval step elapsed start).support) :
    E.retained intermediate ≤ E.bound (E.extent start + horizon * E.increment) :=
  (E.covers intermediate).trans (E.monotone
    (prefix_bound step E.extent E.increment E.grows horizon elapsed hElapsed start intermediate h))

/-- An early stopping boundary is charged at its actual elapsed time. -/
theorem at_boundary (boundary : State → Bool) (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    E.retained result.1 ≤ E.bound (E.extent start + result.2 * E.increment) :=
  (E.covers result.1).trans (E.monotone
    (boundary_endpoint step E.extent E.increment E.grows boundary fuel start result h))

/-- Any monotone change of units preserves the complete resource bound. -/
def mapUnits (units : Nat → Nat) (hUnits : Monotone units) : Envelope step where
  extent := E.extent
  retained := fun state => units (E.retained state)
  bound := fun extent => units (E.bound extent)
  monotone := hUnits.comp E.monotone
  covers := fun state => hUnits (E.covers state)
  increment := E.increment
  grows := E.grows

end Envelope
end Foundation.Probability.TimedExecution.ResourceGrowth
