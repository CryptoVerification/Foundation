import Foundation.Quantum.QKD.FullReconciledHash
import Foundation.Quantum.QKD.PairwiseReconciledRestoration

/-! Exact identification of the public-record-driven full algorithm with
the already proved selected-position decoder/check/PA. The test set condition
is discharged on the actual measurement decoder, not an entropy premise. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem coordinate_tested {m : Nat} (c : PairwiseSampling.Configuration m)
    (minKey tolerance : Nat) (p : (qubits m).Basis × (qubits m).Basis) :
    (coordinateRaw c minKey tolerance p).transcript.tested = c.2 := by
  simp only [coordinateRaw, decodeRawLabel, BB84DeferredRaw.recoverLabel,
    BB84DeferredRaw.rawLabel, Equiv.symm_apply_apply, RawProtocol.output]

theorem full_fixed_restore {n tag length : Nat} {X : Type} [Fintype X] {e : Space}
    (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State X e) (f : X → RawProtocol.Output (BB84SiftedInput.selectedCount M))
    (hf : ∀ x, (f x).transcript.tested = T) (s : Hashing.RawSeed n tag) :
    FullReconciledHash.fixed (length := length) (relabel ρ (fun x => BB84SiftedInput.restoreOutput M θ (f x))) s =
      restorePublic M θ (ReconciledHash.fixed (length := length) M T (relabel ρ f) s) := by
  classical
  unfold FullReconciledHash.fixed ReconciledHash.fixed restorePublic CommonKey.publicProcess
  simp only [restrict_relabel, seed_relabel, relabel_comp]
  simp only [Function.comp_def, FullRawReconciliation.bobKey_restore,
    FullRawReconciliation.publicMessage_restore, hf]
  simp only [RawReconciliation.output, BB84SiftedInput.restoreOutput,
    PairwiseExpandedVerification.restoreRecord, RawReconciliation.publicMessage, RawReconciliation.message]

theorem full_average_restore {n tag length : Nat} {X : Type} [Fintype X] {e : Space}
    (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (T : Finset (Fin (BB84SiftedInput.selectedCount M)))
    (ρ : State X e) (f : X → RawProtocol.Output (BB84SiftedInput.selectedCount M))
    (hf : ∀ x, (f x).transcript.tested = T) :
    FullReconciledHash.average (tag := tag) (length := length)
      (relabel ρ (fun x => BB84SiftedInput.restoreOutput M θ (f x))) =
      restorePublic M θ (ReconciledHash.average (tag := tag) (length := length) M T (relabel ρ f)) := by
  classical
  unfold FullReconciledHash.average ReconciledHash.average
  simp_rw [full_fixed_restore M θ T ρ f hf]
  unfold restorePublic CommonKey.publicProcess
  rw [mixture_relabel]

theorem full_raw_average {n tag length : Nat} {e : Space} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    FullReconciledHash.average (tag := tag) (length := length)
      (relabel (ofCQ (rawState v hv k gap minKey tolerance c)) (BB84SiftedInput.restoreOutput M θ)) =
      restorePublic M θ (rawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c) := by
  rw [rawAverage_process, rawState_coordinates, relabel_comp]
  exact full_average_restore M θ c.2 _ _ (coordinate_tested c minKey tolerance)

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
