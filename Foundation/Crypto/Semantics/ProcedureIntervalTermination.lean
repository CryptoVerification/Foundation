import Foundation.Crypto.Semantics.IterationTermination
import Foundation.Crypto.Semantics.ProcedureStage

/-! Ordinary source stopping certificates survive compression into real
execution intervals and transfer to another machine. Boundaries here are
actual terminals; intermediate query boundaries require a separate handler. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v
set_option backward.isDefEq.respectTransparency false
variable {Source : Type u} {Target : Type v}
    (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceTerminal : Source → Bool) (targetTerminal : Target → Bool)
    (embed : Source → Target)
    (hTerminal : ∀ source, targetTerminal (embed source) = sourceTerminal source)
    (hStep : ∀ source, sourceTerminal source = false → targetStep (embed source) = (sourceStep source).map embed)
    (hSourceAbsorb : ∀ source, sourceTerminal source = true → sourceStep source = PMF.pure source)
    (hTargetAbsorb : ∀ target, targetTerminal target = true → targetStep target = PMF.pure target)

include hSourceAbsorb hTargetAbsorb in
/-- Derive stopping of interval iteration from the original source's
bounded-step proof. Positive interval fuel is essential before termination. -/
theorem interval_stops_of_source (fuel : Nat) (hFuel : 0 < fuel) (start : Source)
    (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ final ∈ (eval sourceStep bound start).support, sourceTerminal final = true)
    (final : Source)
    (hFinal : final ∈ (eval (interval sourceStep targetStep sourceTerminal targetTerminal embed
      hTerminal hStep fuel).semantics rounds start).support) : sourceTerminal final = true := by
  have hAllStep : ∀ source, targetStep (embed source) = (sourceStep source).map embed := by
    intro source
    cases ht : sourceTerminal source with
    | false => exact hStep source ht
    | true =>
        rw [hSourceAbsorb source ht, PMF.pure_map]
        exact hTargetAbsorb (embed source) ((hTerminal source).trans ht)
  have hMap := eval_map sourceStep targetStep embed (fun source => (hAllStep source).symm) bound start
  have hTargetStop : ∀ target ∈ (eval targetStep bound (embed start)).support, targetTerminal target = true := by
    intro target hs
    rw [← hMap, PMF.mem_support_map_iff] at hs
    obtain ⟨source, hs, he⟩ := hs
    subst target
    rw [hTerminal]
    exact hStop source hs
  have hProgress : ∀ input, targetTerminal (embed input) = false →
      ∀ result ∈ (runToBoundary sourceStep sourceTerminal fuel input).support, 0 < result.2 := by
    intro input ht result hs
    rw [hTerminal] at ht
    exact runToBoundary_progress sourceStep sourceTerminal fuel hFuel input ht result hs
  have h := stops_of_machine (interval sourceStep targetStep sourceTerminal targetTerminal embed hTerminal hStep fuel)
    (operational_interval sourceStep sourceTerminal targetTerminal embed hTerminal hStep fuel)
    (fun _ _ _ => rfl) targetTerminal hTargetAbsorb hProgress start bound rounds hRounds hTargetStop final hFinal
  exact (hTerminal final).symm.trans h

include hSourceAbsorb hTargetAbsorb in
/-- Whole original target execution after a proved number of interval
rounds. Returns and costs refer to real steps, and no padding is introduced. -/
theorem interval_iteration_run (fuel : Nat) (hFuel : 0 < fuel) (start : Source)
    (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ final ∈ (eval sourceStep bound start).support, sourceTerminal final = true)
    (horizon : Nat) (hBudget : rounds * fuel ≤ horizon) :
    eval targetStep horizon (embed start) =
      (eval (interval sourceStep targetStep sourceTerminal targetTerminal embed hTerminal hStep fuel).semantics
        rounds start).map embed := by
  have hFinal : ∀ final ∈ (eval
      (interval sourceStep targetStep sourceTerminal targetTerminal embed hTerminal hStep fuel).semantics
      rounds start).support, targetStep (embed final) = PMF.pure (embed final) := by
    intro final hs
    apply hTargetAbsorb (embed final)
    rw [hTerminal]
    exact interval_stops_of_source sourceStep targetStep sourceTerminal targetTerminal embed hTerminal hStep
      hSourceAbsorb hTargetAbsorb fuel hFuel start bound rounds hRounds hStop final hs
  exact Stage.iterateProcedure_final
    (interval sourceStep targetStep sourceTerminal targetTerminal embed hTerminal hStep fuel)
    (fun _ => rfl) (fun _ _ => rfl) fuel (fun _ => Nat.le_refl _) rounds start hFinal horizon hBudget

end Foundation.Probability.TimedExecution.Procedure
