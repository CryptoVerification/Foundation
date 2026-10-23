import Foundation.Crypto.Semantics.Oracle.ReificationExecution

/-! Prefix reasoning for the original timed oracle machine. Native work and
padding keep the transcript; an oracle step only prepends its actual pair.
Every supported bounded prefix extends to a supported later execution.
-/
namespace CryptoOracle.Interactive.Reification
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
universe u

theorem step_trace {State : Type u} (code : Code) (oracle : BitOracle State)
    (start next : Configuration State) (supported : next ∈ (timedStep code oracle start).support) :
    start.reverseTrace ⊆ next.reverseTrace := by
  by_cases halted : terminal start.control = true
  · simp only [timedStep, halted, if_true, PMF.mem_support_pure_iff] at supported
    subst next
    exact List.Subset.refl _
  · simp only [timedStep, halted, Bool.false_eq_true, if_false, perform] at supported
    cases selected : action code start.control with
    | deterministic target =>
        simp only [selected, PMF.mem_support_pure_iff] at supported
        subst next
        exact List.Subset.refl _
    | random zero one =>
        rw [selected, PMF.mem_support_map_iff] at supported
        obtain ⟨coin, _, rfl⟩ := supported
        exact List.Subset.refl _
    | oracleCall machine request =>
        rw [selected, PMF.mem_support_map_iff] at supported
        obtain ⟨answer, _, rfl⟩ := supported
        intro entry member
        exact List.mem_cons_of_mem _ member

theorem eval_trace {State : Type u} (code : Code) (oracle : BitOracle State) (fuel : Nat)
    (start final : Configuration State)
    (supported : final ∈ (TimedExecution.eval (timedStep code oracle) fuel start).support) :
    start.reverseTrace ⊆ final.reverseTrace := by
  induction fuel generalizing start with
  | zero =>
      simp only [TimedExecution.eval, PMF.mem_support_pure_iff] at supported
      subst final
      exact List.Subset.refl _
  | succ fuel ih =>
      rw [TimedExecution.eval, PMF.mem_support_bind_iff] at supported
      obtain ⟨middle, first, rest⟩ := supported
      intro entry member
      exact (ih middle rest) ((step_trace code oracle start middle first) member)

theorem extend_prefix {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel horizon : Nat) (within : fuel ≤ horizon) (start current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (timedStep code oracle) fuel start).support) :
    ∃ final ∈ (TimedExecution.eval (timedStep code oracle) horizon start).support,
      current.reverseTrace ⊆ final.reverseTrace := by
  obtain ⟨final, tail⟩ := PMF.support_nonempty
    (TimedExecution.eval (timedStep code oracle) (horizon - fuel) current)
  refine ⟨final, ?_, eval_trace code oracle (horizon - fuel) current final tail⟩
  rw [show horizon = fuel + (horizon - fuel) by omega, TimedExecution.eval_add, PMF.mem_support_bind_iff]
  exact ⟨current, supported, tail⟩

end CryptoOracle.Interactive.Reification
