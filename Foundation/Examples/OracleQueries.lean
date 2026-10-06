import Foundation.Crypto.Semantics.Oracle.QuerySecurity

namespace CryptoOracle.Examples

open Foundation.Probability Machine
open scoped ENNReal

/-- The second query depends on the first oracle response. -/
def adaptive : Program Bool Bool Bool :=
  .query false fun first => .query first fun second => .done second

noncomputable def countingOracle (firstResponse : Bool) : Oracle Bool Bool Nat :=
  fun state request => PMF.pure (state + 1, if state = 0 then firstResponse else request)

theorem adaptive_two_queries : adaptive.BoundedQueries 2 :=
  .query false _ 1 (fun first => .query first _ 0 (fun second => .done second 0))

example : ¬ adaptive.BoundedQueries 1 := by
  intro h
  cases h with
  | query _ _ _ hNext =>
      have hSecond := hNext true
      cases hSecond

/-- Requests adapt to responses, and the hidden state is not reset. -/
theorem adaptive_left_run : adaptive.run (countingOracle true) 0 =
    PMF.pure (⟨true, 2, [(false, true), (true, true)]⟩ : Outcome Bool Bool Bool Nat) := by
  simp [Program.run, adaptive, countingOracle, PMF.pure_map]

theorem adaptive_right_run : adaptive.run (countingOracle false) 0 =
    PMF.pure (⟨false, 2, [(false, false), (false, false)]⟩ : Outcome Bool Bool Bool Nat) := by
  simp [Program.run, adaptive, countingOracle, PMF.pure_map]

def randomAdaptive : Program Bool Bool Bool :=
  .coin fun bit => if bit then adaptive else .done false

theorem randomAdaptive_two_queries : randomAdaptive.BoundedQueries 2 := by
  apply Program.BoundedQueries.coin
  intro bit
  cases bit
  · exact .done false 2
  · exact adaptive_two_queries

example (outcome : Outcome Bool Bool Bool Nat)
    (h : outcome ∈ (randomAdaptive.run (countingOracle true) 0).support) :
    outcome.trace.length ≤ 2 :=
  randomAdaptive_two_queries.trace_length_le _ _ _ h

/-- Public instances are finite values; oracle functions are experiment data. -/
noncomputable def protocol : Protocol Bool Bool Nat where
  Instance := fun _ => Unit
  games _ _ := ⟨countingOracle true, countingOracle false, 0, 0⟩

example : (queryClass protocol (fun _ => 2)).admissible
    (fun _ => ()) (fun _ => adaptive) := fun _ => adaptive_two_queries

example : ¬ (queryClass protocol (fun _ => 1)).admissible
    (fun _ => ()) (fun _ => adaptive) := by
  intro h
  have hOne := h 0
  cases hOne with
  | query _ _ _ hNext =>
      have hSecond := hNext true
      cases hSecond

/-- The same program whose queries are certified is executed by the goal. -/
example (n : Nat) : (goal protocol).advantage n () adaptive = 1 := by
  change probabilityGap
    (eventProb ((adaptive.run (countingOracle true) 0).map Outcome.result) (· = true))
    (eventProb ((adaptive.run (countingOracle false) 0).map Outcome.result) (· = true)) = 1
  rw [adaptive_left_run, adaptive_right_run]
  simp [PMF.pure_map, eventProb, probabilityGap]

/-- Without access, even these perfectly distinguishable oracles are secure. -/
example : BoundedByOnWithin (goal protocol) (queryClass protocol (fun _ => 0))
    (fun _ => ()) (fun _ => 0) := zeroQueries_secure protocol (fun _ => ())

/-- The query-preservation obligation can allow a larger target bound. -/
noncomputable def relaxQueries
    (J : MachineAdversaryInterface (goal protocol)) (R : ResourceBounds) :
    QueryReduction protocol protocol (Reduction.id (goal protocol)) J J R R
      (fun _ => 1) (fun _ => 2) where
  machine := Reduction.ResourceProgramReduction.id J R
  queries := ⟨fun _ _ h n => (h n).mono (by decide : 1 ≤ 2)⟩

example (J : MachineAdversaryInterface (goal protocol)) (R : ResourceBounds)
    (ε : Nat → ℝ≥0∞)
    (h : ResourceQuerySecure J R (fun _ => 2) (fun _ => ()) ε) :
    ResourceQuerySecure J R (fun _ => 1) (fun _ => ()) ε :=
  (relaxQueries J R).secure (fun _ => ()) ε h

example (J : MachineAdversaryInterface (goal protocol)) (R : ResourceBounds)
    (ε : Nat → ℝ≥0∞)
    (h : ResourceQuerySecure J R (fun _ => 2) (fun _ => ()) ε) :
    ResourceQuerySecure J R (fun _ => 1) (fun _ => ()) ε :=
  ((relaxQueries J R).comp (QueryReduction.id J R (fun _ => 2))).secure (fun _ => ()) ε h

end CryptoOracle.Examples
