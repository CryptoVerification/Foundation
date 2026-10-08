import Foundation.Crypto.Semantics.BoundaryReachability

/-! Recover an actual first-arrival time from adjacent execution horizons.
At an absorbing boundary, being outside one step before universal arrival
rules out every earlier arrival. This is independent of a machine encoding
or a local countdown clock. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

theorem runToBoundary_fixed_time_of_adjacent (step : State → PMF State)
    (boundary : State → Bool) (start : State) (before : Nat)
    (absorbing : ∀ state, boundary state = true → step state = PMF.pure state)
    (active : ∀ state ∈ (eval step before start).support, boundary state = false)
    (complete : ∀ state ∈ (eval step (before + 1) start).support, boundary state = true)
    (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary (before + 1) start).support) :
    result.2 = before + 1 := by
  have hBound := runToBoundary_bounded step boundary (before + 1) start result hResult
  have hStop := runToBoundary_completes step boundary (before + 1) start complete result hResult
  have hReach := runToBoundary_reachable step boundary (before + 1) start result hResult
  by_contra hTime
  have hLe : result.2 ≤ before := by omega
  have hEarlier : result.1 ∈ (eval step before start).support := by
    rw [show before = result.2 + (before - result.2) by omega, eval_add,
      PMF.mem_support_bind_iff]
    refine ⟨result.1, hReach, ?_⟩
    rw [Block.eval_of_absorbing result.1 (absorbing result.1 hStop)]
    simp
  rw [active result.1 hEarlier] at hStop
  contradiction

theorem runToBoundary_joint_of_adjacent (step : State → PMF State)
    (boundary : State → Bool) (start : State) (before : Nat)
    (absorbing : ∀ state, boundary state = true → step state = PMF.pure state)
    (active : ∀ state ∈ (eval step before start).support, boundary state = false)
    (complete : ∀ state ∈ (eval step (before + 1) start).support, boundary state = true) :
    runToBoundary step boundary (before + 1) start =
      (eval step (before + 1) start).map (fun state => (state, before + 1)) := by
  have hMarginal := (Block.stopped step boundary (before + 1) start).final_law
    (fun result hResult => absorbing result.1
      (runToBoundary_completes step boundary (before + 1) start complete result hResult))
    (before + 1) (Nat.le_refl _)
  rw [hMarginal, PMF.map_comp]
  conv_lhs => rw [← PMF.bind_pure (runToBoundary step boundary (before + 1) start)]
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  change PMF.pure result = PMF.pure (result.1, before + 1)
  rw [← runToBoundary_fixed_time_of_adjacent step boundary start before absorbing active complete result hResult]

end Foundation.Probability.TimedExecution
