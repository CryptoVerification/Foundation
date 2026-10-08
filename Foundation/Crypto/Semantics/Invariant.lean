import Foundation.Crypto.Semantics.TimedExecution

/-! Support-based invariants for arbitrary probabilistic transition systems.
These laws preserve full states; no restriction to a cryptographic scheme or
particular history encoding is imposed. -/
namespace Foundation.Probability.TimedExecution
universe u v
variable {State : Type u} {Target : Type v}

def Preserves (step : State → PMF State) (property : State → Prop) : Prop :=
  ∀ start, property start → ∀ final ∈ (step start).support, property final

theorem eval_preserves (step : State → PMF State) (property : State → Prop)
    (hStep : Preserves step property) (fuel : Nat) (start final : State)
    (hStart : property start) (hFinal : final ∈ (eval step fuel start).support) : property final := by
  induction fuel generalizing start with
  | zero =>
      simp only [eval, PMF.mem_support_pure_iff] at hFinal
      subst final
      exact hStart
  | succ fuel ih =>
      rw [eval, PMF.mem_support_bind_iff] at hFinal
      obtain ⟨middle, hMiddle, hFinal⟩ := hFinal
      exact ih middle (hStep start hStart middle hMiddle) hFinal

theorem boundary_preserves (step : State → PMF State) (property : State → Prop)
    (hStep : Preserves step property) (boundary : State → Bool) (fuel : Nat)
    (start : State) (result : State × Nat) (hStart : property start)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) : property result.1 := by
  induction fuel generalizing start result with
  | zero =>
      simp only [runToBoundary, PMF.mem_support_pure_iff] at hResult
      subst result
      exact hStart
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at hResult
        subst result
        exact hStart
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_bind_iff] at hResult
        obtain ⟨middle, hMiddle, hMap⟩ := hResult
        rw [PMF.mem_support_map_iff] at hMap
        obtain ⟨tail, hTail, he⟩ := hMap
        subst result
        exact ih middle tail (hStep start hStart middle hMiddle) hTail

/-- A distributional realization transports a full-state invariant to the
actual implementation. The invariant must hold at every supported source. -/
theorem realized_invariant (logical : PMF State) (actual : PMF Target)
    (embed : State → Target) (property : Target → Prop)
    (hRealizes : actual = logical.map embed)
    (hLogical : ∀ state ∈ logical.support, property (embed state))
    (final : Target) (hFinal : final ∈ actual.support) : property final := by
  rw [hRealizes, PMF.mem_support_map_iff] at hFinal
  obtain ⟨source, hSource, he⟩ := hFinal
  subst final
  exact hLogical source hSource

end Foundation.Probability.TimedExecution
