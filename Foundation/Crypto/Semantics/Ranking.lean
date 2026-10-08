import Foundation.Crypto.Semantics.Invariant
import Foundation.Crypto.Semantics.BoundaryReachability
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Bounded first arrival from a natural-number ranking on admissible states.
Only transitions that remain outside the boundary must decrease the rank.
The boundary may be active in the enclosing machine. No absorption, global
termination on malformed states, or expected-time assumption is used. -/
namespace Foundation.Probability.TimedExecution.Ranking
universe u
variable {State : Type u} (step : State → PMF State) (boundary : State → Bool)
    (invariant : State → Prop) (rank : State → Nat)
    (hPreserves : ∀ start, invariant start → boundary start = false →
      ∀ target ∈ (step start).support, invariant target)
    (hDecrease : ∀ start, invariant start → boundary start = false →
      ∀ target ∈ (step start).support, boundary target = false → rank target < rank start)

include hPreserves hDecrease in
/-- Every branch reaches the boundary within `rank start + 1` steps.
The extra step allows rank-zero active states to move directly to the boundary. -/
theorem completes (fuel : Nat) (start : State) (hStart : invariant start)
    (hFuel : rank start < fuel) (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) : boundary result.1 = true := by
  induction fuel generalizing start result with
  | zero => omega
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · rw [runToBoundary_stopped step boundary (fuel + 1) start hb,
          PMF.mem_support_pure_iff] at hResult
        subst result
        exact hb
      · have ha : boundary start = false := by cases hh : boundary start <;> simp_all
        simp only [runToBoundary, ha, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_bind_iff] at hResult
        obtain ⟨middle, hm, hResult⟩ := hResult
        rw [PMF.mem_support_map_iff] at hResult
        obtain ⟨tail, ht, he⟩ := hResult
        subst result
        by_cases hMiddle : boundary middle = true
        · rw [runToBoundary_stopped step boundary fuel middle hMiddle,
            PMF.mem_support_pure_iff] at ht
          subst tail
          exact hMiddle
        · have hMiddleFalse : boundary middle = false := by
            cases hh : boundary middle <;> simp_all
          have hd := hDecrease start hStart ha middle hm hMiddleFalse
          exact ih middle (hPreserves start hStart ha middle hm) (by omega) tail ht

include hPreserves in
/-- Invariance is needed only before the boundary, never for the caller's
later transitions from an active return state. -/
theorem preserved (fuel : Nat) (start : State) (hStart : invariant start)
    (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) : invariant result.1 := by
  induction fuel generalizing start result with
  | zero =>
      rw [runToBoundary, PMF.mem_support_pure_iff] at hResult
      subst result
      exact hStart
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · rw [runToBoundary_stopped step boundary (fuel + 1) start hb,
          PMF.mem_support_pure_iff] at hResult
        subst result
        exact hStart
      · have ha : boundary start = false := by cases hh : boundary start <;> simp_all
        simp only [runToBoundary, ha, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_bind_iff] at hResult
        obtain ⟨middle, hm, hResult⟩ := hResult
        rw [PMF.mem_support_map_iff] at hResult
        obtain ⟨tail, ht, he⟩ := hResult
        subst result
        exact ih middle (hPreserves start hStart ha middle hm) tail ht

/-- A raw boundary interval with an input-dependent fuel budget. Its outcome
retains actual first-arrival costs, even when arrival is earlier than the cap. -/
noncomputable def raw : Procedure step {state // invariant state} State where
  entry := Subtype.val
  exit := fun _ state => state
  semantics := fun input => (runToBoundary step boundary (rank input.val + 1) input.val).map Prod.fst
  costed := fun input => runToBoundary step boundary (rank input.val + 1) input.val
  budget := fun input => rank input.val + 1
  bounded := fun input => runToBoundary_bounded step boundary (rank input.val + 1) input.val
  correct := fun _ => rfl
  law := fun input horizon hTime => runToBoundary_law step boundary (rank input.val + 1) horizon input.val hTime

include hPreserves hDecrease in
private theorem supported (input : {state // invariant state}) (state : State)
    (h : state ∈ ((raw step boundary invariant rank).semantics input).support) :
    invariant state ∧ boundary state = true := by
  change state ∈ ((runToBoundary step boundary (rank input.val + 1) input.val).map Prod.fst).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, hr, rfl⟩ := h
  exact ⟨preserved step boundary invariant hPreserves _ _ input.property _ hr,
    completes step boundary invariant rank hPreserves hDecrease _ _ input.property (by omega) result hr⟩

/-- A completed, invariant-certified physical endpoint. Proofs add no steps. -/
noncomputable def procedure : Procedure step {state // invariant state}
    {state // invariant state ∧ boundary state = true} :=
  (raw step boundary invariant rank).certify _
    (supported step boundary invariant rank hPreserves hDecrease)

theorem budget (input : {state // invariant state}) :
    (procedure step boundary invariant rank hPreserves hDecrease).budget input = rank input.val + 1 := rfl

theorem exit (input : {state // invariant state})
    (output : {state // invariant state ∧ boundary state = true}) :
    (procedure step boundary invariant rank hPreserves hDecrease).exit input output = output.val := rfl

/-- Erasure recovers the joint law of full endpoints and actual arrival times. -/
theorem costed (input : {state // invariant state}) :
    ((procedure step boundary invariant rank hPreserves hDecrease).costed input).map
      (fun result => (result.1.val, result.2)) =
      runToBoundary step boundary (rank input.val + 1) input.val :=
  Procedure.certify_costed _ _ _ input

/-- Each reported endpoint really occurs at its reported cost. -/
theorem operational : Procedure.Operational
    (procedure step boundary invariant rank hPreserves hDecrease) := by
  apply Procedure.operational_certify
  intro input result hr
  exact runToBoundary_reachable step boundary _ _ result hr

end Foundation.Probability.TimedExecution.Ranking
