import Foundation.Crypto.Semantics.ExecutionStage

/-! Adaptive composition with a state-dependent remaining budget. Each
supported stage exit must leave enough certified budget for the continuation.
The potential is an upper bound, not a runtime counter or padding schedule. -/
namespace Foundation.Probability.TimedExecution.Stage.Potential
universe u v
variable {Source : Type u} {Target : Type v} {step : Target → PMF Target}
    {embed : Source → Target}
    (next : ∀ source, Stage step embed source) (potential : Source → Nat)
    (hConsume : ∀ source result, result ∈ (next source).outcome.support →
      (next source).budget + potential result.1 ≤ potential source)

include hConsume in
theorem budget_le (source : Source) : (next source).budget ≤ potential source := by
  obtain ⟨result, h⟩ := (next source).outcome.support_nonempty
  have hc := hConsume source result h
  omega

noncomputable def iterateAux : (count : Nat) → (start : Source) →
    {stage : Stage step embed start // stage.budget = potential start}
  | 0, start => ⟨(Stage.identity step embed start).resize (potential start) (Nat.zero_le _), rfl⟩
  | count + 1, start =>
      let rest := fun source => (iterateAux count source).val
      let full := (next start).compose rest (potential start - (next start).budget) (by
        intro result h
        have hc := hConsume start result h
        rw [(iterateAux count result.1).property]
        omega)
      ⟨full, by
        change (next start).budget + (potential start - (next start).budget) = potential start
        have hb := budget_le next potential hConsume start
        omega⟩

noncomputable def iterate (count : Nat) (start : Source) :=
  (iterateAux next potential hConsume count start).val

theorem iterate_budget (count : Nat) (start : Source) :
    (iterate next potential hConsume count start).budget = potential start :=
  (iterateAux next potential hConsume count start).property

theorem iterate_distribution (sourceStep : Source → PMF Source)
    (hStep : ∀ source, (next source).outcome.map Prod.fst = sourceStep source)
    (count : Nat) (start : Source) :
    (iterate next potential hConsume count start).outcome.map Prod.fst = eval sourceStep count start := by
  induction count generalizing start with
  | zero => simp [iterate, iterateAux, Stage.identity, Stage.resize, eval, PMF.pure_map]
  | succ count ih =>
      change ((next start).outcome.bind (fun middle =>
        (iterate next potential hConsume count middle.1).outcome.map
          (fun final => (final.1, middle.2 + final.2)))).map Prod.fst = _
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      change ((next start).outcome.bind (fun middle =>
        (iterate next potential hConsume count middle.1).outcome.map Prod.fst)) = _
      simp only [ih]
      change ((next start).outcome.bind (eval sourceStep count ∘ Prod.fst)) = _
      rw [← PMF.bind_map, hStep]
      rfl

/-- Actual joint costs are added; resizing changes only the certificate. -/
theorem iterate_costed_succ (count : Nat) (start : Source) :
    (iterate next potential hConsume (count + 1) start).outcome =
      (next start).outcome.bind (fun first =>
        (iterate next potential hConsume count first.1).outcome.map
          (fun second => (second.1, first.2 + second.2))) := rfl

include hConsume in
theorem final_run (sourceStep : Source → PMF Source)
    (hStep : ∀ source, (next source).outcome.map Prod.fst = sourceStep source)
    (count : Nat) (start : Source)
    (hFinal : ∀ final ∈ (eval sourceStep count start).support,
      step (embed final) = PMF.pure (embed final))
    (horizon : Nat) (hBudget : potential start ≤ horizon) :
    eval step horizon (embed start) = (eval sourceStep count start).map embed := by
  have hd := iterate_distribution next potential hConsume sourceStep hStep count start
  have ha : ∀ result ∈ (iterate next potential hConsume count start).outcome.support,
      step (embed result.1) = PMF.pure (embed result.1) := by
    intro result h
    apply hFinal result.1
    rw [← hd, PMF.mem_support_map_iff]
    exact ⟨result, h, rfl⟩
  rw [(iterate next potential hConsume count start).final_law ha horizon
    (by rw [iterate_budget]; exact hBudget)]
  rw [← hd, PMF.map_comp]
  rfl

end Foundation.Probability.TimedExecution.Stage.Potential
