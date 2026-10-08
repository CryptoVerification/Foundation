import Foundation.Crypto.Semantics.BoundaryStability

/-! A local certificate of exact stopping time for a probabilistic system.
Every supported step outside the boundary consumes exactly one unit. This
is stronger than a decreasing rank or a common termination upper bound. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

structure ExactBoundaryClock (step : State → PMF State) (boundary : State → Bool) where
  valid : State → Prop
  remaining : State → Nat
  terminal : ∀ state, valid state → (boundary state = true ↔ remaining state = 0)
  transition : ∀ state, valid state → boundary state = false →
    ∀ next, next ∈ (step state).support → valid next ∧ remaining next + 1 = remaining state

namespace ExactBoundaryClock
variable {step : State → PMF State} {boundary : State → Bool} (clock : ExactBoundaryClock step boundary)

theorem supported (fuel : Nat) (start : State) (hValid : clock.valid start)
    (hFuel : clock.remaining start ≤ fuel) (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) :
    clock.valid result.1 ∧ boundary result.1 = true ∧ result.2 = clock.remaining start := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at hResult
      subst result
      exact ⟨hValid, (clock.terminal start hValid).mpr (by omega), by omega⟩
  | succ fuel ih =>
      cases hBoundary : boundary start with
      | true =>
          rw [runToBoundary_stopped step boundary _ start hBoundary, PMF.mem_support_pure_iff] at hResult
          subst result
          exact ⟨hValid, hBoundary, ((clock.terminal start hValid).mp hBoundary).symm⟩
      | false =>
          simp only [runToBoundary, hBoundary, Bool.false_eq_true, ↓reduceIte,
            PMF.mem_support_bind_iff] at hResult
          obtain ⟨next, hNext, hRest⟩ := hResult
          rw [PMF.mem_support_map_iff] at hRest
          obtain ⟨final, hFinal, rfl⟩ := hRest
          obtain ⟨hNextValid, hClock⟩ := clock.transition start hValid hBoundary next hNext
          obtain ⟨hFinalValid, hFinalBoundary, hTime⟩ := ih next hNextValid (by omega) final hFinal
          exact ⟨hFinalValid, hFinalBoundary, by dsimp; omega⟩

theorem fixed_time (fuel : Nat) (start : State) (hValid : clock.valid start)
    (hFuel : clock.remaining start ≤ fuel) (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) :
    result.2 = clock.remaining start :=
  (clock.supported fuel start hValid hFuel result hResult).2.2

theorem joint (fuel : Nat) (start : State) (hValid : clock.valid start)
    (hFuel : clock.remaining start ≤ fuel) :
    runToBoundary step boundary fuel start =
      ((runToBoundary step boundary fuel start).map Prod.fst).map (fun state => (state, clock.remaining start)) := by
  rw [PMF.map_comp]
  conv_lhs => rw [← PMF.map_id (runToBoundary step boundary fuel start)]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  change PMF.pure result = PMF.pure (result.1, clock.remaining start)
  have hTime := clock.fixed_time fuel start hValid hFuel result hResult
  cases result with
  | mk state time => dsimp at hTime ⊢; rw [hTime]

end ExactBoundaryClock
end Foundation.Probability.TimedExecution
