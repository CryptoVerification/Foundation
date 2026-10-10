import Foundation.Crypto.Semantics.Oracle.Stopping
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Probability bounds for state-dependent tests immediately before adaptive
queries. The monitor is proof instrumentation: its flag is never passed to the
program. Prefix extraction keeps the actual state at each test time. -/
namespace CryptoOracle.Program

open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Request Response Result State : Type}

/-- Analysis stops before the first hit, without issuing that request. -/
noncomputable def firstHit (hit : State → Request → Bool)
    (oracle : Oracle Request Response State) (state : State) :
    Program Request Response Result → ProbComp Bool
  | .done _ => PMF.pure false
  | .query request next => if hit state request then PMF.pure true else
      (oracle state request).bind (fun answer => firstHit hit oracle answer.1 (next answer.2))
  | .coin next => sampleBit.bind (fun bit => firstHit hit oracle state (next bit))

/-- The actual full interaction may continue after a hit. Only the interpreter
holds the extra flag; the adaptive program still receives just the response. -/
noncomputable def monitorOracle (hit : State → Request → Bool)
    (oracle : Oracle Request Response State) : Oracle Request Response (State × Bool) :=
  fun (state, marked) request => (oracle state request).map (fun answer =>
    ((answer.1, marked || hit state request), answer.2))

def prefixHit (hit : State → Request → Bool)
    (out : Outcome Request Response (Option Request) State) : Prop :=
  ∃ request, out.result = some request ∧ hit out.state request = true

/-- Erasing the flag preserves the complete result, state and public trace. -/
theorem monitor_run_erase (hit : State → Request → Bool) (oracle : Oracle Request Response State)
    (program : Program Request Response Result) (state : State) (marked : Bool) :
    (program.run (monitorOracle hit oracle) (state, marked)).map (mapState Prod.fst) =
      program.run oracle state := by
  apply run_state_map
  intro source request
  simp only [monitorOracle, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- A false final monitor flag implies a false initial flag, even when the
adaptive program continues after a hit. -/
theorem monitor_run_unmarked (hit : State → Request → Bool) (oracle : Oracle Request Response State)
    (program : Program Request Response Result) (state : State) (marked : Bool)
    (out : Outcome Request Response Result (State × Bool))
    (support : out ∈ (program.run (monitorOracle hit oracle) (state, marked)).support)
    (unmarked : out.state.2 = false) : marked = false := by
  induction program generalizing state marked out with
  | done result =>
      rw [run, PMF.mem_support_pure_iff] at support
      subst out
      exact unmarked
  | coin next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit state marked out reachable unmarked
  | query request next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, tailSupport⟩ := support
      rw [monitorOracle, PMF.mem_support_map_iff] at reachable
      obtain ⟨response, _, rfl⟩ := reachable
      rw [PMF.mem_support_map_iff] at tailSupport
      obtain ⟨tail, tailSupport, rfl⟩ := tailSupport
      exact (Bool.or_eq_false_iff.mp
        (ih response.2 response.1 (marked || hit state request) tail tailSupport unmarked)).1

/-- Stopping and the full flagging execution have exactly the same hit law. -/
theorem monitor_firstHit (hit : State → Request → Bool) (oracle : Oracle Request Response State)
    (program : Program Request Response Result) (state : State) (marked : Bool) :
    (program.run (monitorOracle hit oracle) (state, marked)).map (fun out => out.state.2) =
      (firstHit hit oracle state program).map (fun result => marked || result) := by
  induction program generalizing state marked with
  | done result => simp [run, firstHit, PMF.pure_map]
  | coin next ih =>
      simp only [run, firstHit, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state marked
  | query request next ih =>
      simp only [run, monitorOracle, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      simp_rw [ih]
      cases test : hit state request <;>
        simp [firstHit, test, PMF.map, Function.comp_def]

private theorem weighted_sum {A : Type} (law : ProbComp A) (values : A → Nat → ℝ≥0∞) (q : Nat) :
    (∑' a, law a * ∑ k ∈ Finset.range q, values a k) =
      ∑ k ∈ Finset.range q, ∑' a, law a * values a k := by
  induction q with
  | zero => simp
  | succ q ih => simp only [Finset.sum_range_succ, mul_add, ENNReal.tsum_add, ih]

/-- Every hit occurs at one of the actual query prefixes. This union bound
requires no independence between tests at different times. -/
theorem firstHit_prefix_bound (hit : State → Request → Bool) (oracle : Oracle Request Response State)
    {program : Program Request Response Result} {q : Nat} (bound : program.BoundedQueries q) (state : State) :
    eventProb (firstHit hit oracle state program) (· = true) ≤
      ∑ k ∈ Finset.range q, eventProb ((queryPrefix k program).run oracle state) (prefixHit hit) := by
  induction bound generalizing state with
  | done result q =>
      simp [firstHit, queryPrefix, run, eventProb, prefixHit]
  | coin next q bound ih =>
      simp only [firstHit, eventProb_bind_eq]
      calc
        _ ≤ ∑' bit, sampleBit bit * ∑ k ∈ Finset.range q,
              eventProb ((queryPrefix k (next bit)).run oracle state) (prefixHit hit) :=
          ENNReal.tsum_le_tsum (fun bit => mul_le_mul' (le_refl _) (ih bit state))
        _ = _ := by
          rw [weighted_sum]
          simp only [queryPrefix, run, eventProb_bind_eq]
  | query request next q bound ih =>
      rw [Finset.sum_range_succ']
      cases test : hit state request with
      | true =>
          simp only [firstHit, test, ↓reduceIte]
          have head : eventProb ((queryPrefix 0 (.query request next)).run oracle state) (prefixHit hit) = 1 := by
            simp [queryPrefix, run, prefixHit, test, eventProb]
          rw [head]
          simp [eventProb]
      | false =>
          simp only [firstHit, test, Bool.false_eq_true, ↓reduceIte, eventProb_bind_eq]
          have head : eventProb ((queryPrefix 0 (.query request next)).run oracle state) (prefixHit hit) = 0 := by
            simp [queryPrefix, run, prefixHit, test, eventProb]
          rw [head, add_zero]
          calc
            _ ≤ ∑' answer, (oracle state request) answer * ∑ k ∈ Finset.range q,
                  eventProb ((queryPrefix k (next answer.2)).run oracle answer.1) (prefixHit hit) :=
              ENNReal.tsum_le_tsum (fun answer => mul_le_mul' (le_refl _) (ih answer.2 answer.1))
            _ = _ := by
              rw [weighted_sum]
              apply Finset.sum_congr rfl
              intro k hk
              simp only [queryPrefix, run, eventProb_bind_eq]
              apply tsum_congr
              intro answer
              rw [eventProb_map]
              rfl

/-- A hidden environment can correlate all query times. A uniform bound on
each mixed prefix test still bounds the probability of ever hitting by q*error. -/
theorem firstHit_mixed_bound {Environment : Type} (environment : ProbComp Environment)
    (oracle : Environment → Oracle Request Response State) (hit : Environment → State → Request → Bool)
    {program : Program Request Response Result} {q : Nat} (bound : program.BoundedQueries q)
    (state : State) (error : ℝ≥0∞)
    (prefixBound : ∀ k < q,
      eventProb (environment.bind (fun hidden =>
        ((queryPrefix k program).run (oracle hidden) state).map (fun out => (hidden, out))))
        (fun pair => prefixHit (hit pair.1) pair.2) ≤ error) :
    eventProb (environment.bind (fun hidden => firstHit (hit hidden) (oracle hidden) state program)) (· = true) ≤
      (q : ℝ≥0∞) * error := by
  rw [eventProb_bind_eq]
  calc
    _ ≤ ∑' hidden, environment hidden * ∑ k ∈ Finset.range q,
          eventProb ((queryPrefix k program).run (oracle hidden) state) (prefixHit (hit hidden)) :=
      ENNReal.tsum_le_tsum (fun hidden => mul_le_mul' (le_refl _) (firstHit_prefix_bound (hit hidden) (oracle hidden) bound state))
    _ = ∑ k ∈ Finset.range q,
          eventProb (environment.bind (fun hidden =>
            ((queryPrefix k program).run (oracle hidden) state).map (fun out => (hidden, out))))
            (fun pair => prefixHit (hit pair.1) pair.2) := by
      rw [weighted_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [eventProb_bind_eq, eventProb_map]
    _ ≤ ∑ _k ∈ Finset.range q, error := Finset.sum_le_sum (fun k hk => prefixBound k (Finset.mem_range.mp hk))
    _ = _ := by simp

end CryptoOracle.Program
