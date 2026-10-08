import Foundation.Crypto.Semantics.TimedExecution

/-! Local resource growth bounds for arbitrary probabilistic machines.
The measure describes the complete physical state chosen by the client.
Bounds hold on every supported branch, and at every inspected prefix.
Boundary execution retains its actual cost rather than charging its budget. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth
universe u
variable {State : Type u} (step : State → PMF State) (size : State → Nat)
  (increment : Nat)
  (localBound : ∀ start next, next ∈ (step start).support →
    size next ≤ size start + increment)

include localBound

theorem endpoint (fuel : Nat) (start finish : State)
    (h : finish ∈ (eval step fuel start).support) :
    size finish ≤ size start + fuel * increment := by
  induction fuel generalizing start finish with
  | zero =>
      rw [eval, PMF.mem_support_pure_iff] at h
      subst finish
      simp
  | succ fuel ih =>
      rw [eval, PMF.mem_support_bind_iff] at h
      obtain ⟨next, hNext, hFinish⟩ := h
      have hFirst := localBound start next hNext
      have hRest := ih next finish hFinish
      rw [Nat.succ_mul]
      omega

/-- Every possible intermediate state respects the same horizon bound.
This bounds peak usage, not merely the final state's usage. -/
theorem prefix_bound (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start intermediate : State)
    (h : intermediate ∈ (eval step elapsed start).support) :
    size intermediate ≤ size start + horizon * increment := by
  have hEnd := endpoint step size increment localBound elapsed start intermediate h
  have hMul := Nat.mul_le_mul_right increment hElapsed
  omega

/-- At an early boundary, charge only the transitions actually taken. -/
theorem boundary_endpoint (boundary : State → Bool) (fuel : Nat)
    (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    size result.1 ≤ size start + result.2 * increment := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      simp
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        simp
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
        obtain ⟨next, hNext, hRest⟩ := h
        rw [PMF.mem_support_map_iff] at hRest
        obtain ⟨final, hFinal, he⟩ := hRest
        subst result
        have hFirst := localBound start next hNext
        have hLast := ih next final hFinal
        simp only [Nat.add_mul, Nat.one_mul]
        omega

end Foundation.Probability.TimedExecution.ResourceGrowth

namespace Foundation.Probability.TimedExecution.ResourceGrowth
universe u
variable {State : Type u}

/-- A resource argument may use a preserved invariant of reachable states.
This does not require a growth bound for malformed or unreachable states. -/
theorem invariant_endpoint (step : State → PMF State) (size : State → Nat)
    (valid : State → Prop) (increment : Nat)
    (localBound : ∀ start, valid start → ∀ next, next ∈ (step start).support →
      valid next ∧ size next ≤ size start + increment)
    (fuel : Nat) (start finish : State) (hStart : valid start)
    (h : finish ∈ (eval step fuel start).support) :
    valid finish ∧ size finish ≤ size start + fuel * increment := by
  induction fuel generalizing start finish with
  | zero =>
      rw [eval, PMF.mem_support_pure_iff] at h
      subst finish
      simpa using hStart
  | succ fuel ih =>
      rw [eval, PMF.mem_support_bind_iff] at h
      obtain ⟨next, hNext, hRest⟩ := h
      obtain ⟨hv, hs⟩ := localBound start hStart next hNext
      obtain ⟨hf, hb⟩ := ih next finish hv hRest
      refine ⟨hf, ?_⟩
      rw [Nat.succ_mul]
      omega

theorem invariant_boundary_endpoint (step : State → PMF State) (size : State → Nat)
    (valid : State → Prop) (increment : Nat)
    (localBound : ∀ start, valid start → ∀ next, next ∈ (step start).support →
      valid next ∧ size next ≤ size start + increment)
    (boundary : State → Bool) (fuel : Nat) (start : State) (result : State × Nat)
    (hStart : valid start)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    valid result.1 ∧ size result.1 ≤ size start + result.2 * increment := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      simpa using hStart
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        simpa using hStart
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
        obtain ⟨next, hNext, hRest⟩ := h
        rw [PMF.mem_support_map_iff] at hRest
        obtain ⟨final, hFinal, he⟩ := hRest
        subst result
        obtain ⟨hv, hs⟩ := localBound start hStart next hNext
        obtain ⟨hf, hl⟩ := ih next final hv hFinal
        refine ⟨hf, ?_⟩
        simp only [Nat.add_mul, Nat.one_mul]
        omega

end Foundation.Probability.TimedExecution.ResourceGrowth
