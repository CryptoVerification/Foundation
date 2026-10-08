import Foundation.Crypto.Semantics.ProcedureIteration
import Foundation.Crypto.Semantics.ProcedureSteps

/-! Repeated contracts may stop at a returned-state boundary. Stopping is
a zero-transition contract at the existing physical state, not a fabricated
halt. The residual law resumes the original machine with the unused fuel. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v
variable {State : Type u} {Value : Type v} {step : State → PMF State}

noncomputable def guard (P : Procedure step Value Value) (stop : Value → Bool) :
    Procedure step Value Value where
  entry := P.entry
  exit := fun input output => if stop input then P.entry output else P.exit input output
  semantics := fun input => if stop input then PMF.pure input else P.semantics input
  costed := fun input => if stop input then PMF.pure (input, 0) else P.costed input
  budget := fun input => if stop input then 0 else P.budget input
  bounded := by
    intro input result hResult
    cases hs : stop input with
    | false =>
        simp only [hs, Bool.false_eq_true, ↓reduceIte] at hResult ⊢
        exact P.bounded input result hResult
    | true =>
        simp only [hs, ↓reduceIte, PMF.mem_support_pure_iff] at hResult
        subst result
        simp
  correct := by
    intro input
    cases hs : stop input <;> simp [P.correct, PMF.pure_map]
  law := by
    intro input horizon hBudget
    cases hs : stop input with
    | true => simp [PMF.pure_bind]
    | false =>
        simp only [hs, Bool.false_eq_true, ↓reduceIte] at hBudget ⊢
        exact P.law input horizon hBudget

variable (P : Procedure step Value Value) (stop : Value → Bool) (bound : Nat)
    (hBound : ∀ input, P.budget input ≤ bound)
    (hReturn : ∀ input output, output ∈ (P.semantics input).support → P.exit input output = P.entry output)

include hBound in
theorem guard_bound (input : Value) : (guard P stop).budget input ≤ bound := by
  cases hs : stop input <;> simp only [guard, hs, Bool.false_eq_true, ↓reduceIte]
  · exact hBound input
  · exact Nat.zero_le _

include hReturn in
theorem guard_return (input output : Value) (h : output ∈ ((guard P stop).semantics input).support) :
    (guard P stop).exit input output = (guard P stop).entry output := by
  cases hs : stop input with
  | true => simp [guard, hs]
  | false =>
      simp only [guard, hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact hReturn input output h

noncomputable def iterateUntil (rounds : Nat) :=
  (guard P stop).iterate bound (guard_bound P stop bound hBound) (guard_return P stop hReturn) rounds

theorem until_budget (rounds : Nat) (input : Value) :
    (iterateUntil P stop bound hBound hReturn rounds).budget input = rounds * bound :=
  iterate_budget _ _ _ _ _ _

theorem until_stopped (rounds : Nat) (input : Value) (hStop : stop input = true) :
    (iterateUntil P stop bound hBound hReturn rounds).costed input = PMF.pure (input, 0) := by
  induction rounds with
  | zero => simp [iterateUntil, iterate, iteration, Procedure.ofFixed, PMF.pure_map]
  | succ rounds ih =>
      unfold iterateUntil
      rw [iterate_costed_succ]
      simp only [guard, hStop, ↓reduceIte, PMF.pure_bind]
      change ((iterateUntil P stop bound hBound hReturn rounds).costed input).map (fun result => (result.1, 0 + result.2)) = _
      rw [ih]
      simp [PMF.pure_map]

variable (actualStep : State → PMF State) (boundary : State → Bool)

noncomputable def stepsUntil (fuel : Nat) :=
  (transition actualStep).iterateUntil boundary 1 (transition_bound actualStep) (transition_return actualStep) fuel

/-- The stopped repeated one-step contracts are exactly first-arrival
execution, including each actual cost and the full physical configuration. -/
theorem stepsUntil_costed (fuel : Nat) (start : State) :
    (stepsUntil actualStep boundary fuel).costed start = runToBoundary actualStep boundary fuel start := by
  induction fuel generalizing start with
  | zero => simp [iterateUntil, iterate, iteration, Procedure.ofFixed, PMF.pure_map, stepsUntil, runToBoundary]
  | succ fuel ih =>
      unfold stepsUntil iterateUntil
      rw [iterate_costed_succ]
      cases hb : boundary start with
      | true =>
          simp only [guard, hb, ↓reduceIte, PMF.pure_bind, Nat.zero_add]
          change ((stepsUntil actualStep boundary fuel).costed start).map id = _
          rw [PMF.map_id, ih]
          cases fuel <;> simp [runToBoundary, hb]
      | false =>
          simp only [guard, hb, Bool.false_eq_true, ↓reduceIte, transition, Procedure.ofFixed,
            PMF.bind_map, Function.comp_def, runToBoundary]
          congr 1
          funext next
          change ((stepsUntil actualStep boundary fuel).costed next).map (fun result => (result.1, 1 + result.2)) = _
          rw [ih]
          simp [Nat.add_comm]

end Foundation.Probability.TimedExecution.Procedure
