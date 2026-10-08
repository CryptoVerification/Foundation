import Foundation.Crypto.Semantics.OneUseCounter

/-! A ghost event counter is bounded by the number of actual transitions.
Counting does not change the machine's marginal execution or runtime cost. -/
namespace Foundation.Probability.TimedExecution.EventCount
universe u
variable {State : Type u} (step : State → PMF State) (event : State → Bool)

theorem growth (fuel : Nat) (start result : State × Nat)
    (h : result ∈ (eval (OneUseCounter.countedStep step event) fuel start).support) :
    result.2 ≤ start.2 + fuel := by
  induction fuel generalizing start result with
  | zero =>
      rw [eval, PMF.mem_support_pure_iff] at h
      subst result
      omega
  | succ fuel ih =>
      rw [eval, PMF.mem_support_bind_iff] at h
      obtain ⟨middle, hMiddle, hResult⟩ := h
      rw [OneUseCounter.countedStep, PMF.mem_support_map_iff] at hMiddle
      obtain ⟨next, _, he⟩ := hMiddle
      subst middle
      have hb := ih _ _ hResult
      cases hEvent : event start.1 <;> simp [hEvent] at hb <;> omega

theorem bound (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (eval (OneUseCounter.countedStep step event) fuel (start, 0)).support) : result.2 ≤ fuel := by
  simpa using growth step event fuel (start, 0) result h
end Foundation.Probability.TimedExecution.EventCount
