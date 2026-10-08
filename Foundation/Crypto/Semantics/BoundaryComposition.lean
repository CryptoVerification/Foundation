import Foundation.Crypto.Semantics.BoundaryStability

/-! Sequential first-arrival laws with branch-dependent actual durations.
Before the first boundary the final boundary must be excluded on a preserved
invariant. Both finite stages must complete; timeout is not a handoff.
The second stage starts at the actual supported first result. Neither
boundary must be absorbing, and unused analysis fuel is not charged. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}
set_option maxHeartbeats 1000000

theorem runToBoundary_compose (step : State → PMF State)
    (firstBoundary finalBoundary : State → Bool) (valid : State → Prop)
    (preserves : ∀ state, valid state → firstBoundary state = false →
      ∀ next ∈ (step state).support, valid next)
    (excludes : ∀ state, valid state → firstBoundary state = false → finalBoundary state = false)
    (firstFuel lastFuel : Nat) (start : State) (hValid : valid start)
    (firstComplete : ∀ middle ∈ (runToBoundary step firstBoundary firstFuel start).support,
      firstBoundary middle.1 = true)
    (lastComplete : ∀ middle ∈ (runToBoundary step firstBoundary firstFuel start).support,
      ∀ result ∈ (runToBoundary step finalBoundary lastFuel middle.1).support,
        finalBoundary result.1 = true) :
    runToBoundary step finalBoundary (firstFuel + lastFuel) start =
      (runToBoundary step firstBoundary firstFuel start).bind (fun middle =>
        (runToBoundary step finalBoundary lastFuel middle.1).map
          (fun result => (result.1, middle.2 + result.2))) := by
  induction firstFuel generalizing start with
  | zero =>
      simp only [runToBoundary, PMF.pure_bind, Nat.zero_add]
      exact (PMF.map_id _).symm
  | succ firstFuel ih =>
      cases hFirst : firstBoundary start with
      | true =>
          rw [runToBoundary_stopped step firstBoundary (firstFuel + 1) start hFirst, PMF.pure_bind]
          simp only [Nat.zero_add]
          have complete : ∀ result ∈ (runToBoundary step finalBoundary lastFuel start).support,
              finalBoundary result.1 = true := by
            intro result hResult
            apply lastComplete (start, 0) _ result hResult
            rw [runToBoundary_stopped step firstBoundary (firstFuel + 1) start hFirst]
            simp
          rw [runToBoundary_fuel_stable step finalBoundary lastFuel
            (firstFuel + 1 + lastFuel) start (by omega) complete]
          exact (PMF.map_id _).symm
      | false =>
          have hFinal := excludes start hValid hFirst
          simp only [Nat.succ_add, runToBoundary, hFirst, hFinal,
            Bool.false_eq_true, ↓reduceIte, PMF.bind_map, PMF.bind_bind]
          rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
          congr 1
          funext next hNext
          have liftSupport (middle : State × Nat)
              (hMiddle : middle ∈ (runToBoundary step firstBoundary firstFuel next).support) :
              (middle.1, middle.2 + 1) ∈
                (runToBoundary step firstBoundary (firstFuel + 1) start).support := by
            simp only [runToBoundary, hFirst, Bool.false_eq_true, ↓reduceIte,
              PMF.mem_support_bind_iff]
            refine ⟨next, hNext, ?_⟩
            rw [PMF.mem_support_map_iff]
            exact ⟨middle, hMiddle, rfl⟩
          rw [ih next (preserves start hValid hFirst next hNext)
            (fun middle hMiddle => firstComplete (middle.1, middle.2 + 1) (liftSupport middle hMiddle))
            (fun middle hMiddle => lastComplete (middle.1, middle.2 + 1) (liftSupport middle hMiddle)), PMF.map_bind]
          congr 1
          funext middle
          simp only [PMF.map_comp, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Foundation.Probability.TimedExecution
