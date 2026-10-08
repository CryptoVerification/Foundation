import Foundation.Crypto.Semantics.ResourceGrowth

/-! Resource growth up to an execution boundary. Local bounds are needed
only before that boundary, where transitions are actually executed. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth
universe u
variable {State : Type u} (step : State → PMF State) (boundary : State → Bool) (size : State → Nat)
    (increment : Nat)
    (hLocal : ∀ start, boundary start = false → ∀ next ∈ (step start).support,
      size next ≤ size start + increment)

include hLocal

theorem boundary_before (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    size result.1 ≤ size start + result.2 * increment := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      simp
  | succ fuel ih =>
      cases hb : boundary start with
      | true =>
          simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
          subst result
          simp
      | false =>
          simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
          obtain ⟨next, hNext, hRest⟩ := h
          rw [PMF.mem_support_map_iff] at hRest
          obtain ⟨final, hFinal, he⟩ := hRest
          subst result
          have hFirst := hLocal start hb next hNext
          have hLast := ih next final hFinal
          simp only [Nat.add_mul, Nat.one_mul]
          omega

theorem boundary_before_cap (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    size result.1 ≤ size start + fuel * increment := by
  have he := boundary_before step boundary size increment hLocal fuel start result h
  have ht := runToBoundary_bounded step boundary fuel start result h
  have hm := Nat.mul_le_mul_right increment ht
  omega

end Foundation.Probability.TimedExecution.ResourceGrowth
