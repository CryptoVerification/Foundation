import Foundation.Crypto.Semantics.TimedExecution

/-! A boundary result is reachable in exactly its reported actual cost.
Fuel exhaustion and successful boundary arrival remain distinct. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

theorem runToBoundary_reachable (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    result.1 ∈ (eval step result.2 start).support := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      simp [eval]
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        simp [eval]
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
        obtain ⟨next, hNext, hRest⟩ := h
        rw [PMF.mem_support_map_iff] at hRest
        obtain ⟨final, hFinal, he⟩ := hRest
        subst result
        simp only [eval, PMF.mem_support_bind_iff]
        exact ⟨next, hNext, ih next final hFinal⟩

theorem runToBoundary_stopped (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) (hStop : boundary start = true) :
    runToBoundary step boundary fuel start = PMF.pure (start, 0) := by
  cases fuel <;> simp [runToBoundary, hStop]

/-- Positive fuel executes at least one real transition when the entry is
outside the boundary. Budget alone is not a progress claim at a boundary. -/
theorem runToBoundary_progress (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (hFuel : 0 < fuel) (start : State) (hStart : boundary start = false)
    (result : State × Nat) (h : result ∈ (runToBoundary step boundary fuel start).support) :
    0 < result.2 := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      rw [runToBoundary, hStart] at h
      simp only [Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
      obtain ⟨next, _, hs⟩ := h
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨final, _, he⟩ := hs
      subst result
      omega

/-- A successful first arrival has an actual reachable last transition
from outside the boundary. This excludes a fabricated acceptance event. -/
theorem runToBoundary_last_step (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) (result : State × Nat)
    (hStart : boundary start = false) (hFinal : boundary result.1 = true)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    ∃ before, before ∈ (eval step (result.2 - 1) start).support ∧
      boundary before = false ∧ result.1 ∈ (step before).support := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      simp [hStart] at hFinal
  | succ fuel ih =>
      simp only [runToBoundary, hStart, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
      obtain ⟨next, hNext, hRest⟩ := h
      rw [PMF.mem_support_map_iff] at hRest
      obtain ⟨final, hResult, he⟩ := hRest
      subst result
      cases hb : boundary next with
      | true =>
          rw [runToBoundary_stopped step boundary fuel next hb, PMF.mem_support_pure_iff] at hResult
          subst final
          exact ⟨start, by simp [eval], hStart, hNext⟩
      | false =>
          obtain ⟨before, hBefore, hBoundary, hLast⟩ := ih next final hb hFinal hResult
          have hPositive : 0 < final.2 := by
            by_contra hn
            have hz : final.2 = 0 := by omega
            have hr := runToBoundary_reachable step boundary fuel next final hResult
            rw [hz, eval, PMF.mem_support_pure_iff] at hr
            rw [hr, hb] at hFinal
            contradiction
          refine ⟨before, ?_, hBoundary, hLast⟩
          have hCost : final.2 + 1 - 1 = (final.2 - 1) + 1 := by omega
          rw [hCost, eval, PMF.mem_support_bind_iff]
          exact ⟨next, hNext, hBefore⟩

end Foundation.Probability.TimedExecution
