import Foundation.Examples.RankedVariableTime
import Foundation.Crypto.Semantics.ExactBoundaryClock

/-! A common upper bound is insufficient for an exact clock. The existing
randomized native example stops in either three or four real transitions. -/
namespace Foundation.Examples.ExactClockRejection
open Machine Foundation.Probability TimedExecution

theorem no_clock_within_four (input : Tape) :
    ¬ ∃ clock : ExactBoundaryClock (stepPMF RankedVariableTime.code) Configuration.halted,
      clock.valid (RankedVariableTime.initial input) ∧ clock.remaining (RankedVariableTime.initial input) ≤ 4 := by
  rintro ⟨clock, valid, bounded⟩
  have hFalse : (RankedVariableTime.finish input false, 3) ∈
      (runToBoundary (stepPMF RankedVariableTime.code) Configuration.halted 4 (RankedVariableTime.initial input)).support := by
    rw [RankedVariableTime.boundary_law, PMF.mem_support_map_iff]
    exact ⟨false, by simp [sampleBit, uniform], rfl⟩
  have hTrue : (RankedVariableTime.finish input true, 4) ∈
      (runToBoundary (stepPMF RankedVariableTime.code) Configuration.halted 4 (RankedVariableTime.initial input)).support := by
    rw [RankedVariableTime.boundary_law, PMF.mem_support_map_iff]
    exact ⟨true, by simp [sampleBit, uniform], rfl⟩
  have hThree := clock.fixed_time 4 _ valid bounded _ hFalse
  have hFour := clock.fixed_time 4 _ valid bounded _ hTrue
  dsimp at hThree hFour
  omega

end Foundation.Examples.ExactClockRejection
