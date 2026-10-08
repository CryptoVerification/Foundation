import Foundation.Crypto.Semantics.ExactBoundaryClock

/-! Reuse exact clocks across an invertible change of state representation.
The target must execute one transition for every source transition with
the same probabilities. This does not certify a slower implementation. -/
namespace Foundation.Probability.TimedExecution.ExactBoundaryClock
universe u v
variable {Source : Type u} {Target : Type v}
    {sourceStep : Source → PMF Source} {sourceBoundary : Source → Bool}

noncomputable def transport (clock : ExactBoundaryClock sourceStep sourceBoundary)
    (equiv : Source ≃ Target) (targetStep : Target → PMF Target) (targetBoundary : Target → Bool)
    (sameBoundary : ∀ source, targetBoundary (equiv source) = sourceBoundary source)
    (sameStep : ∀ source, targetStep (equiv source) = (sourceStep source).map equiv) :
    ExactBoundaryClock targetStep targetBoundary where
  valid := fun target => clock.valid (equiv.symm target)
  remaining := fun target => clock.remaining (equiv.symm target)
  terminal := by
    intro target hValid
    have hBoundary := sameBoundary (equiv.symm target)
    rw [equiv.apply_symm_apply] at hBoundary
    rw [hBoundary]
    exact clock.terminal _ hValid
  transition := by
    intro target hValid hActive next hNext
    have hBoundary := sameBoundary (equiv.symm target)
    rw [equiv.apply_symm_apply] at hBoundary
    have hStep := sameStep (equiv.symm target)
    rw [equiv.apply_symm_apply] at hStep
    rw [hStep, PMF.mem_support_map_iff] at hNext
    obtain ⟨sourceNext, hSourceNext, rfl⟩ := hNext
    simpa only [equiv.symm_apply_apply] using
      clock.transition (equiv.symm target) hValid (hBoundary.symm.trans hActive) sourceNext hSourceNext

end Foundation.Probability.TimedExecution.ExactBoundaryClock
