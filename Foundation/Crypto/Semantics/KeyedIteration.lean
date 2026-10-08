import Foundation.Crypto.Semantics.CostedIteration

/-! A common public costed kernel preserves independence of a retained key
through adaptive stopped iteration. Keys may have any prior distribution.
The conclusion is a joint distribution, so public timing is included. -/
namespace Foundation.Probability.KeyedIteration
universe u v w x
variable {Key : Type u} {Value : Type v} {Public : Type w}

noncomputable def joint (keys : PMF Key) (execution : Key → PMF Value) : PMF (Key × Value) :=
  keys.bind (fun key => (execution key).map (fun result => (key, result)))

/-- Independence as exact factorization. No conditioning on an event of
zero probability and no uniformity assumption on the prior are needed. -/
theorem joint_independent (keys : PMF Key) (execution : Key → PMF Value)
    (common : PMF Value) (h : ∀ key, execution key = common) :
    joint keys execution = keys.bind (fun key => common.map (fun result => (key, result))) := by
  unfold joint
  congr 1
  funext key
  rw [h key]

theorem joint_observe {Observed : Type x} (keys : PMF Key) (execution : Key → PMF Value)
    (common : PMF Value) (h : ∀ key, execution key = common)
    (observer : Value → PMF Observed) :
    (joint keys execution).bind (fun result => (observer result.2).map (fun seen => (result.1, seen))) =
      keys.bind (fun key => (common.bind observer).map (fun seen => (key, seen))) := by
  rw [joint_independent keys execution common h]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]

end Foundation.Probability.KeyedIteration

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {Key : Type u} {State : Type v} {Value : Type w} {Public : Type x}
    {step : State → PMF State}

/-- Sample the key once, execute a family of real contracts, and retain
the key label with the public result and actual accumulated cost. -/
theorem iterateUntil_key_independent (keys : PMF Key) (P : Key → Procedure step Value Value)
    (bound : Nat) (hBound : ∀ key input, (P key).budget input ≤ bound)
    (hReturn : ∀ key input output, output ∈ ((P key).semantics input).support →
      (P key).exit input output = (P key).entry output)
    (stop : Value → Bool) (publicStop : Public → Bool)
    (publicKernel : Public → PMF (Public × Nat)) (view : Value → Public)
    (hStop : ∀ input, stop input = publicStop (view input))
    (hRound : ∀ key input, ((P key).costed input).map (CostedIteration.project view) = publicKernel (view input))
    (start : Key → Value) (publicStart : Public) (hStart : ∀ key, view (start key) = publicStart)
    (rounds : Nat) :
    KeyedIteration.joint keys (fun key =>
      (((P key).iterateUntil stop bound (hBound key) (hReturn key) rounds).costed (start key)).map
        (CostedIteration.project view)) =
      keys.bind (fun key =>
        (CostedIteration.eval (CostedIteration.guarded publicKernel publicStop) rounds publicStart).map
          (fun result => (key, result))) := by
  apply KeyedIteration.joint_independent
  intro key
  rw [iterateUntil_public_cost (P key) bound (hBound key) (hReturn key)
    stop publicStop publicKernel view hStop (hRound key), hStart key]

end Foundation.Probability.TimedExecution.Procedure
