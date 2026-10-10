import Foundation.Crypto.Semantics.BoundaryExactTime

/-! Congruence of a finite execution known to remain outside an absorbing
boundary. Only steps that stay active need to agree. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

theorem eval_congr_of_active_final (source target : State → PMF State) (boundary : State → Bool)
    (absorbing : ∀ state, boundary state = true → source state = PMF.pure state)
    (same : ∀ state, boundary state = false →
      (∀ next ∈ (source state).support, boundary next = false) → target state = source state)
    (fuel : Nat) (start : State)
    (active : ∀ result ∈ (eval source fuel start).support, boundary result = false) :
    eval target fuel start = eval source fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have childActive (next : State) (support : next ∈ (source start).support) :
          ∀ result ∈ (eval source fuel next).support, boundary result = false := by
        intro result reachable
        apply active result
        rw [eval, PMF.mem_support_bind_iff]
        exact ⟨next, support, reachable⟩
      have nextActive : ∀ next ∈ (source start).support, boundary next = false := by
        intro next support
        cases hb : boundary next with
        | false => rfl
        | true =>
            have retained := Block.eval_of_absorbing next (absorbing next hb) fuel
            have reachable : next ∈ (eval source fuel next).support := by rw [retained]; simp
            have impossible := childActive next support next reachable
            rw [hb] at impossible
            contradiction
      have startActive : boundary start = false := by
        cases hb : boundary start with
        | false => rfl
        | true =>
            have supported : start ∈ (source start).support := by rw [absorbing start hb]; simp
            have impossible := nextActive start supported
            rw [hb] at impossible
            contradiction
      simp only [eval]
      rw [same start startActive nextActive, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next support
      exact ih next (childActive next support)

/-- An absorbing boundary not reached at the final horizon has not been
reached earlier. The stopped execution therefore charges the whole horizon. -/
theorem runToBoundary_joint_of_active_final (step : State → PMF State) (boundary : State → Bool)
    (absorbing : ∀ state, boundary state = true → step state = PMF.pure state)
    (fuel : Nat) (start : State)
    (active : ∀ result ∈ (eval step fuel start).support, boundary result = false) :
    runToBoundary step boundary fuel start = (eval step fuel start).map (fun state => (state, fuel)) := by
  induction fuel generalizing start with
  | zero => simp [runToBoundary, eval, PMF.pure_map]
  | succ fuel ih =>
      have startActive : boundary start = false := by
        cases stopped : boundary start with
        | false => rfl
        | true =>
            have supported : start ∈ (eval step (fuel + 1) start).support := by
              rw [Block.eval_of_absorbing start (absorbing start stopped)]
              simp
            have impossible := active start supported
            rw [stopped] at impossible
            contradiction
      have childActive (next : State) (support : next ∈ (step start).support) :
          ∀ result ∈ (eval step fuel next).support, boundary result = false := by
        intro result reachable
        apply active result
        rw [eval, PMF.mem_support_bind_iff]
        exact ⟨next, support, reachable⟩
      simp only [runToBoundary, startActive, Bool.false_eq_true, ↓reduceIte, eval, PMF.map_bind]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next support
      rw [ih next (childActive next support), PMF.map_comp]
      rfl

end Foundation.Probability.TimedExecution
