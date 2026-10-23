import Foundation.Crypto.Semantics.Oracle.QueryPrefix

/-! Suspend immediately BEFORE the first changed request. The exact remaining
controller and its real prefix state/trace are retained. This is an ordinary
program construction, not a higher-dimensional separation result. -/
namespace CryptoOracle.Program
open Foundation.Probability
variable {Request Response Result State : Type} [DecidableEq Request]

def pauseBefore (changed : Finset Request) : Program Request Response Result →
    Program Request Response (Program Request Response Result)
  | .done result => .done (.done result)
  | .coin next => .coin fun bit => pauseBefore changed (next bit)
  | .query request next => if request ∈ changed then .done (.query request next)
      else .query request fun response => pauseBefore changed (next response)

theorem pauseBefore_resume (changed : Finset Request) (program : Program Request Response Result) :
    (pauseBefore changed program).bind id = program := by
  induction program with
  | done result => rfl
  | coin next ih => simp only [pauseBefore, bind]; congr 1; funext bit; exact ih bit
  | query request next ih =>
      by_cases member : request ∈ changed
      · simp [pauseBefore, member, bind]
      · simp only [pauseBefore, if_neg member, bind]; congr 1; funext response; exact ih response

/-- No finite response enumeration or query-count approximation is needed. -/
theorem pauseBefore_same (changed : Finset Request) (program : Program Request Response Result)
    (left right : Oracle Request Response State)
    (agree : ∀ request ∉ changed, ∀ state, left state request = right state request)
    (state : State) :
    (pauseBefore changed program).run left state = (pauseBefore changed program).run right state := by
  induction program generalizing state with
  | done result => rfl
  | coin next ih =>
      simp only [pauseBefore, run]; congr 1; funext bit; exact ih bit state
  | query request next ih =>
      by_cases member : request ∈ changed
      · simp only [pauseBefore, if_pos member, run]
      · simp only [pauseBefore, if_neg member, run, agree request member state]
        congr 1; funext answer
        rw [ih answer.2 answer.1]

noncomputable def resumePast (world : Oracle Request Response State)
    (past : Outcome Request Response (Program Request Response Result) State) :=
  (past.result.run world past.state).map fun last => {last with trace := past.trace ++ last.trace}

theorem pauseBefore_continuation (changed : Finset Request) (program : Program Request Response Result)
    (world : Oracle Request Response State) (state : State) :
    ((pauseBefore changed program).run world state).bind (resumePast world) = program.run world state := by
  have law := run_bind (pauseBefore changed program) id world state
  rw [pauseBefore_resume] at law
  exact law.symm

/-- Recheck suffixes only at the actually supported change frontier. The old
prefix law, local coins, state, and ordered transcript are reused exactly. -/
theorem repair_at_frontier (changed : Finset Request) (program : Program Request Response Result)
    (left right : Oracle Request Response State)
    (agree : ∀ request ∉ changed, ∀ state, left state request = right state request)
    (state : State)
    (repair : ∀ past ∈ ((pauseBefore changed program).run left state).support,
      resumePast left past = resumePast right past) :
    program.run left state = program.run right state := by
  rw [← pauseBefore_continuation changed program left state,
    ← pauseBefore_continuation changed program right state,
    ← pauseBefore_same changed program left right agree state]
  exact bind_congr_of_support _ _ _ repair

/-- Different representations may have distinct raw states. Repair only the
requested observations, retaining the original prefix in each suffix law. -/
theorem repair_observation_at_frontier {Observation : Type}
    (changed : Finset Request) (program : Program Request Response Result)
    (left right : Oracle Request Response State)
    (agree : ∀ request ∉ changed, ∀ state, left state request = right state request)
    (state : State) (observeLeft observeRight : Outcome Request Response Result State → Observation)
    (repair : ∀ past ∈ ((pauseBefore changed program).run left state).support,
      (resumePast left past).map observeLeft = (resumePast right past).map observeRight) :
    (program.run left state).map observeLeft = (program.run right state).map observeRight := by
  rw [← pauseBefore_continuation changed program left state,
    ← pauseBefore_continuation changed program right state,
    ← pauseBefore_same changed program left right agree state, PMF.map_bind, PMF.map_bind]
  exact bind_congr_of_support _ _ _ repair

/-- Prefix invariant obligations concern ONLY unchanged requests, even when
the invariant fails for the modified operation itself. -/
theorem pauseBefore_preserves (changed : Finset Request) (program : Program Request Response Result)
    (world : Oracle Request Response State) (invariant : State → Prop)
    (step : ∀ state, invariant state → ∀ request, request ∉ changed → ∀ answer,
      answer ∈ (world state request).support → invariant answer.1)
    (state : State) (valid : invariant state)
    (past : Outcome Request Response (Program Request Response Result) State)
    (reachable : past ∈ ((pauseBefore changed program).run world state).support) : invariant past.state := by
  induction program generalizing state past with
  | done result =>
      simp only [pauseBefore, run, PMF.mem_support_pure_iff] at reachable
      subst past; exact valid
  | coin next ih =>
      rw [pauseBefore, run, PMF.mem_support_bind_iff] at reachable
      obtain ⟨bit, _, reachable⟩ := reachable
      exact ih bit state valid past reachable
  | query request next ih =>
      by_cases member : request ∈ changed
      · simp only [pauseBefore, if_pos member, run, PMF.mem_support_pure_iff] at reachable
        subst past; exact valid
      · simp only [pauseBefore, if_neg member, run, PMF.mem_support_bind_iff] at reachable
        obtain ⟨answer, supported, reachable⟩ := reachable
        rw [PMF.mem_support_map_iff] at reachable
        obtain ⟨last, reachable, rfl⟩ := reachable
        exact ih answer.2 answer.1 (step state valid request member answer supported) last reachable

/-- A supported suspension is either finished or directly at a changed query.
No claim is made that all syntactic changed requests are reached. -/
theorem pauseBefore_boundary (changed : Finset Request) (program : Program Request Response Result)
    (world : Oracle Request Response State) (state : State)
    (past : Outcome Request Response (Program Request Response Result) State)
    (supported : past ∈ ((pauseBefore changed program).run world state).support) :
    (∃ result, past.result = .done result) ∨
      ∃ request next, request ∈ changed ∧ past.result = .query request next := by
  induction program generalizing state past with
  | done result =>
      simp only [pauseBefore, run, PMF.mem_support_pure_iff] at supported
      subst past; exact Or.inl ⟨result, rfl⟩
  | coin next ih =>
      rw [pauseBefore, run, PMF.mem_support_bind_iff] at supported
      obtain ⟨bit, _, reachable⟩ := supported
      exact ih bit state past reachable
  | query request next ih =>
      by_cases member : request ∈ changed
      · simp only [pauseBefore, if_pos member, run, PMF.mem_support_pure_iff] at supported
        subst past; exact Or.inr ⟨request, next, member, rfl⟩
      · simp only [pauseBefore, if_neg member, run, PMF.mem_support_bind_iff] at supported
        obtain ⟨answer, _, reachable⟩ := supported
        rw [PMF.mem_support_map_iff] at reachable
        obtain ⟨last, reachable, rfl⟩ := reachable
        exact ih answer.2 answer.1 last reachable

/-- A general mixture comparison, with a support-local exceptional set. -/
theorem frontier_mixture_le {Index Value : Type} (law : PMF Index)
    (left right : Index → PMF Value) (event : Value → Prop) (bad : Index → Prop)
    (agree : ∀ index ∈ law.support, ¬ bad index → left index = right index) :
    eventProb (law.bind left) event ≤ eventProb (law.bind right) event + eventProb law bad := by
  classical
  rw [eventProb_bind_eq, eventProb_bind_eq]
  calc
    _ ≤ ∑' index, (law index * eventProb (right index) event +
        if bad index then law index else 0) := by
      apply ENNReal.tsum_le_tsum
      intro index
      by_cases zero : law index = 0
      · simp [zero]
      · by_cases exceptional : bad index
        · simp only [if_pos exceptional]
          calc
            _ ≤ law index * 1 := mul_le_mul' le_rfl (eventProb_le_one _ _)
            _ = law index := mul_one _
            _ ≤ _ := le_add_left le_rfl
        · rw [agree index ((PMF.mem_support_iff _ _).mpr zero) exceptional]
          simp [exceptional]
    _ = _ := by
      rw [ENNReal.tsum_add]
      congr 1
      simp only [eventProb, PMF.toOuterMeasure_apply, Set.indicator_apply,
        Set.mem_ofPred_eq]

/-- A changed request is reached exactly when the retained controller is a
query rather than a completed result. -/
def atChanged (past : Outcome Request Response (Program Request Response Result) State) : Prop :=
  ∃ request next, past.result = .query request next

/-- Ordinary identical-until-change bound for the FULL outcome distribution.
It preserves final state and transcript as well as the caller result. -/
theorem change_frontier_bound (changed : Finset Request) (program : Program Request Response Result)
    (left right : Oracle Request Response State)
    (agree : ∀ request ∉ changed, ∀ state, left state request = right state request)
    (state : State) (event : Outcome Request Response Result State → Prop) :
    eventProb (program.run left state) event ≤ eventProb (program.run right state) event +
      eventProb ((pauseBefore changed program).run left state) atChanged := by
  rw [← pauseBefore_continuation changed program left state,
    ← pauseBefore_continuation changed program right state,
    ← pauseBefore_same changed program left right agree state]
  apply frontier_mixture_le
  intro past reachable safe
  rcases pauseBefore_boundary changed program left state past reachable with ⟨result, completed⟩ | ⟨request, next, _, pending⟩
  · simp only [resumePast, completed, run]
  · exact False.elim (safe ⟨request, next, pending⟩)

end CryptoOracle.Program
