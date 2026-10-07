import Foundation.Crypto.Semantics.TimedExecution

/-! Resource-bounded execution refinements with proof-level source states.
The source coordinate can retain an invariant or private store layout. The
runtime machine executes only its original target transition function. -/
namespace Foundation.Probability.TimedExecution
universe u v
variable {Source : Type u} {Target : Type v}

structure Stage (step : Target → PMF Target) (embed : Source → Target) (start : Source) where
  budget : Nat
  outcome : PMF (Source × Nat)
  bounded : ∀ result ∈ outcome.support, result.2 ≤ budget
  law : ∀ horizon, budget ≤ horizon → eval step horizon (embed start) =
    outcome.bind (fun result => eval step (horizon - result.2) (embed result.1))

namespace Stage
variable {step : Target → PMF Target} {embed : Source → Target} {start : Source}

noncomputable def toBlock (stage : Stage step embed start) : Block step (embed start) where
  budget := stage.budget
  outcome := stage.outcome.map (fun result => (embed result.1, result.2))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_map_iff] at hResult
    obtain ⟨source, hSource, he⟩ := hResult
    subst result
    exact stage.bounded source hSource
  law := by
    intro horizon hHorizon
    rw [stage.law horizon hHorizon, PMF.bind_map]
    rfl

noncomputable def identity (step : Target → PMF Target) (embed : Source → Target) (start : Source) :
    Stage step embed start where
  budget := 0
  outcome := PMF.pure (start, 0)
  bounded := by intro result h; simp only [PMF.mem_support_pure_iff] at h; subst result; exact Nat.le_refl _
  law := by intro horizon h; simp [PMF.pure_bind]

/-- Increase only the certified upper bound, never the actual duration. -/
noncomputable def resize (stage : Stage step embed start) (cap : Nat) (hCap : stage.budget ≤ cap) :
    Stage step embed start where
  budget := cap
  outcome := stage.outcome
  bounded := fun result h => (stage.bounded result h).trans hCap
  law := fun horizon h => stage.law horizon (hCap.trans h)

noncomputable def compose (first : Stage step embed start)
    (next : (source : Source) → Stage step embed source) (cap : Nat)
    (hCap : ∀ middle ∈ first.outcome.support, (next middle.1).budget ≤ cap) : Stage step embed start where
  budget := first.budget + cap
  outcome := first.outcome.bind fun middle => (next middle.1).outcome.map
    (fun final => (final.1, middle.2 + final.2))
  bounded := by
    intro result hResult
    rw [PMF.mem_support_bind_iff] at hResult
    obtain ⟨middle, hMiddle, hMap⟩ := hResult
    rw [PMF.mem_support_map_iff] at hMap
    obtain ⟨final, hFinal, he⟩ := hMap
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

/-- Repeat a real stage while retaining its source coordinate and actual
cost. The multiplication is a bound, not a padding schedule. -/
noncomputable def iterateAux (next : (source : Source) → Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap) :
    (count : Nat) → (start : Source) → { stage : Stage step embed start // stage.budget = count * cap }
  | 0, start => ⟨identity step embed start, by simp [identity]⟩
  | count + 1, start =>
      let first := (next start).resize cap (hCap start)
      let rest := fun source => (iterateAux next cap hCap count source).val
      let full := first.compose rest (count * cap) (by
        intro middle hMiddle
        exact Nat.le_of_eq (iterateAux next cap hCap count middle.1).property)
      ⟨full, by
        change cap + count * cap = (count + 1) * cap
        simp [Nat.add_mul, Nat.add_comm]⟩

noncomputable def iterate (next : (source : Source) → Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap) (count : Nat) (start : Source) :=
  (iterateAux next cap hCap count start).val

theorem iterate_budget (next : (source : Source) → Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap) (count : Nat) (start : Source) :
    (iterate next cap hCap count start).budget = count * cap :=
  (iterateAux next cap hCap count start).property

/-- Matching one-stage source-state distributions suffices for every
finite iteration. All probabilities are retained, including adaptive branches. -/
theorem iterate_distribution (next : (source : Source) → Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap)
    (sourceStep : Source → PMF Source)
    (hStep : ∀ source, (next source).outcome.map Prod.fst = sourceStep source)
    (count : Nat) (start : Source) :
    (iterate next cap hCap count start).outcome.map Prod.fst = eval sourceStep count start := by
  induction count generalizing start with
  | zero => simp [iterate, iterateAux, identity, eval, PMF.pure_map]
  | succ count ih =>
      change ((next start).outcome.bind (fun middle =>
        (iterate next cap hCap count middle.1).outcome.map
          (fun final => (final.1, middle.2 + final.2)))).map Prod.fst = _
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      change ((next start).outcome.bind (fun middle =>
        (iterate next cap hCap count middle.1).outcome.map Prod.fst)) = _
      simp only [ih]
      change ((next start).outcome.bind (eval sourceStep count ∘ Prod.fst)) = _
      rw [← PMF.bind_map, hStep]
      rfl

theorem final_law (stage : Stage step embed start)
    (hAbsorbing : ∀ result ∈ stage.outcome.support, step (embed result.1) = PMF.pure (embed result.1))
    (horizon : Nat) (hBudget : stage.budget ≤ horizon) :
    eval step horizon (embed start) = stage.outcome.map (fun result => embed result.1) := by
  rw [stage.law horizon hBudget, ← PMF.bindOnSupport_eq_bind, PMF.map,
    ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  exact Block.eval_of_absorbing (embed result.1) (hAbsorbing result hResult) _

/-- A source stopping proof yields whole target execution at the composed
budget, provided real one-stage laws have actually been constructed. -/
theorem iterate_final_law (next : (source : Source) → Stage step embed source)
    (cap : Nat) (hCap : ∀ source, (next source).budget ≤ cap)
    (sourceStep : Source → PMF Source)
    (hStep : ∀ source, (next source).outcome.map Prod.fst = sourceStep source)
    (count : Nat) (start : Source)
    (hFinal : ∀ final ∈ (eval sourceStep count start).support, step (embed final) = PMF.pure (embed final))
    (horizon : Nat) (hBudget : count * cap ≤ horizon) :
    eval step horizon (embed start) = (eval sourceStep count start).map embed := by
  have hDistribution := iterate_distribution next cap hCap sourceStep hStep count start
  have hAbsorbing : ∀ result ∈ (iterate next cap hCap count start).outcome.support,
      step (embed result.1) = PMF.pure (embed result.1) := by
    intro result hResult
    apply hFinal result.1
    rw [← hDistribution, PMF.mem_support_map_iff]
    exact ⟨result, hResult, rfl⟩
  rw [(iterate next cap hCap count start).final_law hAbsorbing horizon
    (by rw [iterate_budget]; exact hBudget)]
  rw [← hDistribution, PMF.map_comp]
  rfl

end Stage
end Foundation.Probability.TimedExecution
