import Foundation.Crypto.Semantics.ProcedureReachability
import Foundation.Crypto.Semantics.ProcedureBoundary

/-! Boundary lifting reports actual first-arrival costs, so its operational
reachability follows directly even if the component contract includes padding.
Remembering inputs changes only the logical result, not the reached state. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Source : Type u} {Input : Type v} {Output : Type w} {Target : Type x}
    {sourceStep : Source → PMF Source}

theorem operational_remember (P : Procedure sourceStep Input Output) (hP : Operational P) :
    Operational P.remember := by
  intro input result hs
  change result ∈ ((P.costed input).map (fun original => ((input, original.1), original.2))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  exact hP input original ho

theorem operational_liftBoundary (P : Procedure sourceStep Input Output)
    (sourceBoundary : Source → Bool)
    (hExit : ∀ input output, output ∈ (P.semantics input).support → sourceBoundary (P.exit input output) = true)
    (hAbsorb : ∀ state, sourceBoundary state = true → sourceStep state = PMF.pure state)
    (read : Input → Source → Output) (hRead : ∀ input output, read input (P.exit input output) = output)
    (targetStep : Target → PMF Target) (targetBoundary : Target → Bool) (embed : Source → Target)
    (hBoundary : ∀ state, targetBoundary (embed state) = sourceBoundary state)
    (hStep : ∀ state, sourceBoundary state = false → targetStep (embed state) = (sourceStep state).map embed) :
    Operational (P.liftBoundary sourceBoundary hExit hAbsorb read hRead targetStep targetBoundary embed hBoundary hStep) := by
  intro input result hs
  change result ∈ ((runToBoundary sourceStep sourceBoundary (P.budget input) (P.entry input)).map
    (fun original => (read input original.1, original.2))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨original, ho, he⟩ := hs
  subst result
  change embed (P.exit input (read input original.1)) ∈
    (eval targetStep original.2 (embed (P.entry input))).support
  rw [P.stopped_reader input sourceBoundary (hExit input) hAbsorb (read input) (hRead input) original ho]
  have ht : (embed original.1, original.2) ∈
      (runToBoundary targetStep targetBoundary (P.budget input) (embed (P.entry input))).support := by
    rw [runToBoundary_map sourceStep targetStep sourceBoundary targetBoundary embed hBoundary hStep,
      PMF.mem_support_map_iff]
    exact ⟨original, ho, rfl⟩
  exact runToBoundary_reachable targetStep targetBoundary (P.budget input) (embed (P.entry input))
    (embed original.1, original.2) ht

end Foundation.Probability.TimedExecution.Procedure
