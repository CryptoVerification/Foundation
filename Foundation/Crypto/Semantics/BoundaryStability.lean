import Foundation.Crypto.Semantics.BoundaryReachability

/-! First-arrival distributions compose without charging absorbing padding.
Once every supported result has reached the boundary, a larger analysis
fuel leaves both the reached state and its actual arrival cost unchanged. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

theorem runToBoundary_add (step : State → PMF State) (boundary : State → Bool)
    (first second : Nat) (start : State) :
    runToBoundary step boundary (first + second) start =
      (runToBoundary step boundary first start).bind (fun middle =>
        (runToBoundary step boundary second middle.1).map (fun result => (result.1, middle.2 + result.2))) := by
  induction first generalizing start with
  | zero =>
      simp only [Nat.zero_add, runToBoundary, PMF.pure_bind]
      exact (PMF.map_id _).symm
  | succ first ih =>
      by_cases hStop : boundary start = true
      · rw [runToBoundary_stopped step boundary _ start hStop,
          runToBoundary_stopped step boundary _ start hStop, PMF.pure_bind,
          runToBoundary_stopped step boundary _ start hStop]
        simp only [PMF.pure_map, Nat.zero_add]
      · simp only [Nat.succ_add, runToBoundary, hStop, Bool.false_eq_true, ↓reduceIte,
          PMF.bind_map, PMF.bind_bind]
        congr 1
        funext next
        rw [ih, PMF.map_bind]
        congr 1
        funext middle
        simp only [PMF.map_comp, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem runToBoundary_add_of_complete (step : State → PMF State) (boundary : State → Bool)
    (fuel extra : Nat) (start : State)
    (complete : ∀ result, result ∈ (runToBoundary step boundary fuel start).support → boundary result.1 = true) :
    runToBoundary step boundary (fuel + extra) start = runToBoundary step boundary fuel start := by
  rw [runToBoundary_add]
  conv_rhs => rw [← PMF.bind_pure (runToBoundary step boundary fuel start)]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  rw [runToBoundary_stopped step boundary extra result.1 (complete result hResult), PMF.pure_map]
  simp only [Nat.add_zero, Prod.mk.eta]

theorem runToBoundary_fuel_stable (step : State → PMF State) (boundary : State → Bool)
    (fuel larger : Nat) (start : State) (hFuel : fuel ≤ larger)
    (complete : ∀ result, result ∈ (runToBoundary step boundary fuel start).support → boundary result.1 = true) :
    runToBoundary step boundary larger start = runToBoundary step boundary fuel start := by
  have h := runToBoundary_add_of_complete step boundary fuel (larger - fuel) start complete
  simpa only [Nat.add_sub_of_le hFuel] using h

end Foundation.Probability.TimedExecution
