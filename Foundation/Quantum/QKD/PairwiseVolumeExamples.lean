import Foundation.Quantum.QKD.FullReconciledVolume
import Foundation.Quantum.QKD.PairwiseReconciledExamples

namespace Foundation.Quantum.QKD.PairwiseVolumeExamples
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Counts spheres rather than enumerating the 2^100 binary strings. -/
theorem hundred_radius_two : BinaryWeightVolume.volume 100 2 = 5051 := by
  norm_num [BinaryWeightVolume.volume, Finset.sum_range_succ, Nat.choose]

theorem twelve_radius_four : BinaryWeightVolume.volume 12 4 = 794 := by
  norm_num [BinaryWeightVolume.volume, Finset.sum_range_succ, Nat.choose]

theorem noisy_accepted_support (c : PairwiseSampling.Configuration 12) :
    PairwisePhaseCoordinates.acceptedSupport 3 0 1 1 c ≤ 794 := by
  have h := PairwisePhaseCoordinates.acceptedSupport_le_volume 3 0 1 1 (by decide) c
  norm_num [PairwisePhaseCoordinates.supportRadius] at h
  exact h.trans_eq twelve_radius_four

/-- A computational-basis copying attack is a nontrivial coherent attack.
This small example checks the whole protocol connection, not a useful error. -/
theorem attacked_full_secure :
    IdealKey.Secure (FullReconciledSecurity.realState (tag := 1) (length := 1)
      PairwiseReconciledExamples.attack 1 1 0)
      (1/2 + (2 * Real.sqrt (PairwiseSampling.gapBound 4 1 2) +
        FullReconciledSecurity.globalVolumeError 4 1 1 1 2 1 0)) := by
  have h := FullReconciledSecurity.real_secure_volume (tag := 1) (length := 1)
    PairwiseReconciledExamples.attack 1 2 1 0 (by decide) (by decide)
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.PairwiseVolumeExamples
