import Foundation.Crypto.Semantics.Probability.Comp

/-! Composition of actual probabilistic execution stages with variable costs.
A stage retains its final state and the number of transitions it used. Its
law relates that distribution to the original machine at every later horizon.
Unspent budget continues execution; it is not an artificial stage stutter.
Reaching a designated boundary is a separate completion obligation. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

noncomputable def eval (step : State → PMF State) : Nat → State → PMF State
  | 0, start => PMF.pure start
  | fuel + 1, start => (step start).bind (eval step fuel)

theorem eval_add (step : State → PMF State) (first second : Nat) (start : State) :
    eval step (first + second) start = (eval step first start).bind (eval step second) := by
  induction first generalizing start with
  | zero => simp [eval, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, eval, PMF.bind_bind]
      congr 1
      funext next
      exact ih next

noncomputable def runToBoundary (step : State → PMF State) (boundary : State → Bool) :
    Nat → State → PMF (State × Nat)
  | 0, start => PMF.pure (start, 0)
  | fuel + 1, start =>
      if boundary start then PMF.pure (start, 0)
      else (step start).bind fun next =>
        (runToBoundary step boundary fuel next).map fun result => (result.1, result.2 + 1)

theorem runToBoundary_bounded (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) : result.2 ≤ fuel := by
  induction fuel generalizing start result with
  | zero =>
      simp only [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      exact Nat.le_refl 0
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        exact Nat.zero_le _
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_bind_iff] at h
        obtain ⟨next, _, hm⟩ := h
        rw [PMF.mem_support_map_iff] at hm
        obtain ⟨final, hFinal, hEq⟩ := hm
        subst result
        exact Nat.succ_le_succ (ih next final hFinal)

/-- Resume the original step relation with precisely the budget left after
the stage. This law is valid even when the boundary was not reached. -/
theorem runToBoundary_law (step : State → PMF State) (boundary : State → Bool)
    (fuel horizon : Nat) (start : State) (horizon_ge : fuel ≤ horizon) :
    eval step horizon start =
      (runToBoundary step boundary fuel start).bind (fun result => eval step (horizon - result.2) result.1) := by
  induction fuel generalizing horizon start with
  | zero => simp [runToBoundary, PMF.pure_bind]
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp [runToBoundary, hb, PMF.pure_bind]
      · cases horizon with
        | zero => omega
        | succ horizon =>
            simp only [eval, runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, PMF.bind_bind, PMF.bind_map,
              Function.comp_def, Nat.add_sub_add_right]
            congr 1
            funext next
            exact ih horizon next (by omega)

/-- Embed a stage into a larger machine. Steps need agree only before
the boundary; the larger machine may continue after that boundary. -/
theorem runToBoundary_map {Source : Type*} (sourceStep : Source → PMF Source)
    (targetStep : State → PMF State) (sourceBoundary : Source → Bool)
    (targetBoundary : State → Bool) (embed : Source → State)
    (hBoundary : ∀ source, targetBoundary (embed source) = sourceBoundary source)
    (hStep : ∀ source, sourceBoundary source = false →
      targetStep (embed source) = (sourceStep source).map embed)
    (fuel : Nat) (start : Source) :
    runToBoundary targetStep targetBoundary fuel (embed start) =
      (runToBoundary sourceStep sourceBoundary fuel start).map
        (fun result => (embed result.1, result.2)) := by
  induction fuel generalizing start with
  | zero => simp [runToBoundary, PMF.pure_map]
  | succ fuel ih =>
      cases hb : sourceBoundary start with
      | true => simp [runToBoundary, hBoundary, hb, PMF.pure_map]
      | false =>
          simp only [runToBoundary, hBoundary, hb, Bool.false_eq_true, ↓reduceIte,
            hStep start hb, PMF.bind_map, PMF.map_bind, Function.comp_def, ih, PMF.map_comp]

/-- Every unfinished endpoint used the entire stage budget. -/
theorem boundary_or_exhausted (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (runToBoundary step boundary fuel start).support) :
    boundary result.1 = true ∨ result.2 = fuel := by
  induction fuel generalizing start result with
  | zero =>
      simp only [runToBoundary, PMF.mem_support_pure_iff] at h
      subst result
      exact Or.inr rfl
  | succ fuel ih =>
      by_cases hb : boundary start = true
      · simp only [runToBoundary, hb, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        exact Or.inl hb
      · simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_bind_iff] at h
        obtain ⟨next, _, hm⟩ := h
        rw [PMF.mem_support_map_iff] at hm
        obtain ⟨final, hf, he⟩ := hm
        subst result
        rcases ih next final hf with hb | ht
        · exact Or.inl hb
        · exact Or.inr (congrArg (· + 1) ht)

/-- An ordinary horizon completion proof also certifies the stopped stage.
No absorbing assumption at an intermediate boundary is needed. -/
theorem runToBoundary_completes (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State)
    (hComplete : ∀ final ∈ (eval step fuel start).support, boundary final = true)
    (result : State × Nat)
    (hResult : result ∈ (runToBoundary step boundary fuel start).support) :
    boundary result.1 = true := by
  rcases boundary_or_exhausted step boundary fuel start result hResult with hb | ht
  · exact hb
  · apply hComplete result.1
    rw [runToBoundary_law step boundary fuel fuel start (Nat.le_refl _),
      PMF.mem_support_bind_iff]
    refine ⟨result, hResult, ?_⟩
    simp [ht, eval]

/-- A certificate about real steps. The law is not a claim that arbitrary
host-language code can be executed at its declared budget. -/
structure Block (step : State → PMF State) (start : State) where
  budget : Nat
  outcome : PMF (State × Nat)
  bounded : ∀ result ∈ outcome.support, result.2 ≤ budget
  law : ∀ horizon, budget ≤ horizon → eval step horizon start =
    outcome.bind (fun result => eval step (horizon - result.2) result.1)

namespace Block

noncomputable def stopped (step : State → PMF State) (boundary : State → Bool)
    (fuel : Nat) (start : State) : Block step start where
  budget := fuel
  outcome := runToBoundary step boundary fuel start
  bounded := runToBoundary_bounded step boundary fuel start
  law := fun horizon h => runToBoundary_law step boundary fuel horizon start h

/-- A fixed number of genuine transitions, with no host-code cost
assumption. Intermediate boundary claims are independent of this block. -/
noncomputable def fixed (step : State → PMF State) (fuel : Nat) (start : State) :
    Block step start where
  budget := fuel
  outcome := (eval step fuel start).map (fun final => (final, fuel))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨final, _, he⟩ := hResult
    subst result
    exact Nat.le_refl _
  law := by
    intro horizon hHorizon
    have hh : horizon = fuel + (horizon - fuel) := by omega
    conv_lhs => rw [hh, eval_add]
    rw [PMF.bind_map]
    rfl

def Completes {step : State → PMF State} {start : State} (block : Block step start)
    (boundary : State → Bool) : Prop :=
  ∀ result ∈ block.outcome.support, boundary result.1 = true

/-- Uniform second-stage budget need only hold at reachable first-stage
endpoints. Completion of either stage must be supplied separately. -/
noncomputable def compose {step : State → PMF State} {start : State} (first : Block step start)
    (next : (state : State) → Block step state) (cap : Nat)
    (hCap : ∀ middle ∈ first.outcome.support, (next middle.1).budget ≤ cap) : Block step start where
  budget := first.budget + cap
  outcome := first.outcome.bind fun middle => (next middle.1).outcome.map
    (fun final => (final.1, middle.2 + final.2))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_bind_iff] at hResult
    obtain ⟨middle, hMiddle, hMap⟩ := hResult
    rw [PMF.mem_support_map_iff] at hMap
    obtain ⟨final, hFinal, hEq⟩ := hMap
    subst result
    have hFirst := first.bounded middle hMiddle
    have hSecond := (next middle.1).bounded final hFinal
    have hBudget := hCap middle hMiddle
    omega
  law := by
    intro horizon hHorizon
    rw [first.law horizon (by omega), PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def]
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext middle hMiddle
    have hFirst := first.bounded middle hMiddle
    have hBudget := hCap middle hMiddle
    simpa only [Nat.sub_sub] using (next middle.1).law (horizon - middle.2) (by omega)

theorem compose_completes {step : State → PMF State} {start : State} (first : Block step start)
    (next : (state : State) → Block step state) (cap : Nat)
    (hCap : ∀ middle ∈ first.outcome.support, (next middle.1).budget ≤ cap)
    (boundary : State → Bool)
    (hNext : ∀ middle ∈ first.outcome.support, (next middle.1).Completes boundary) :
    (first.compose next cap hCap).Completes boundary := by
  intro result hResult
  change result ∈ (first.outcome.bind (fun middle => (next middle.1).outcome.map
    (fun final => (final.1, middle.2 + final.2)))).support at hResult
  rw [PMF.mem_support_bind_iff] at hResult
  obtain ⟨middle, hMiddle, hMap⟩ := hResult
  rw [PMF.mem_support_map_iff] at hMap
  obtain ⟨final, hFinal, hEq⟩ := hMap
  subst result
  exact hNext middle hMiddle final hFinal

theorem eval_of_absorbing {step : State → PMF State} (state : State)
    (h : step state = PMF.pure state) (fuel : Nat) : eval step fuel state = PMF.pure state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [eval, h, PMF.pure_bind, ih]

/-- Only final absorbing endpoints justify dropping the residual execution.
The result law retains all branches and their probabilities. -/
theorem final_law {step : State → PMF State} {start : State} (block : Block step start)
    (hAbsorbing : ∀ result ∈ block.outcome.support, step result.1 = PMF.pure result.1)
    (horizon : Nat) (hBudget : block.budget ≤ horizon) :
    eval step horizon start = block.outcome.map Prod.fst := by
  rw [block.law horizon hBudget, ← PMF.bindOnSupport_eq_bind, PMF.map,
    ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  exact eval_of_absorbing result.1 (hAbsorbing result hResult) _

end Block
end Foundation.Probability.TimedExecution
