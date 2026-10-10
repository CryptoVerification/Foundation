import Foundation.Quantum.QKD.PairwiseRawHashExamples

/-! The complete retained error record commutes with the complementary key
gate. This identifies the physical order used by the support certificate with
the retained-record order used by the existing sampling approximation. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

theorem record_key {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    (RetainedControl.channel (fun _ : Fin (count n) => (keyChannel θ).amplify e)).toKraus.apply
      ((first θ e).toKraus.apply ρ) =
        (first θ e).toKraus.apply (((keyChannel θ).amplify e).toKraus.apply ρ) := by
  rw [first, Instrument.retained_post, ← Instrument.record_pre]
  apply Instrument.record_congr
  intro r
  rw [Instrument.post_apply, Instrument.pre_apply]
  exact (branch_key θ e ρ r).symm

theorem rawState_retained {n : Nat} {e : Space}
    (v : (jointSpace n e).Basis → ℂ) (hv : PureProjection.bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    (rawState v hv k gap minKey tolerance c).density.matrix =
      (PairwiseRawPost.afterFirst (PairwiseRecordedSampling.basis c) e c.2 minKey tolerance).toKraus.apply
        ((RetainedControl.channel (fun _ : Fin (count n) =>
          (keyChannel (PairwiseRecordedSampling.basis c)).amplify e)).toKraus.apply
          ((first (PairwiseRecordedSampling.basis c) e).toKraus.apply
            (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
              (PairwiseQuantumSampling.fallback v hv)).matrix)) := by
  rw [record_key]
  exact rawState_physical _ _ _ _ _ _ _

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
