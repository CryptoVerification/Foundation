import Foundation.Quantum.QKD.PairwiseExpandedHash
import Foundation.Quantum.QKD.PairwisePublicSecrecy

/-! Full-position public seeds and restored public records in the same
uniform-key comparison for the selected sampling approximant. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def restoreTranscript {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (t : RawProtocol.PublicRecord (BB84SiftedInput.selectedCount M)) : RawProtocol.PublicRecord n :=
  ⟨θ, BB84SiftingRandomness.bobBases θ M, BB84SiftedInput.liftTest M t.tested,
    BB84SiftedInput.expand M t.aliceTest, BB84SiftedInput.expand M t.bobTest, t.accepted⟩

theorem restore_transcript {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (o : RawProtocol.Output (BB84SiftedInput.selectedCount M)) :
    (BB84SiftedInput.restoreOutput M θ o).transcript = restoreTranscript M θ o.transcript := rfl

def expandedPublishedHash {n length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  PublicRegisterExpose.expose (HashLayout.output (testedSource v hv k gap minKey tolerance c)
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) (expandedHash M c.2))

theorem expanded_published_secrecy {n length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (expandedPublishedHash (length := length) M v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (expandedPublishedHash (length := length) M v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  apply PublicRegisterExpose.secrecy
    (HashLayout.output (testedSource v hv k gap minKey tolerance c) _ (expandedHash M c.2))
    (PublicRegisterExpose.hash_output_diagonal _ (testedSource_diagonal _ _ _ _ _ _ _) _ _) _
  apply HashLayout.secrecy
  exact expandedHashPrivacy M v hv k gap minKey tolerance c

def expandedPublishedRawHash {n length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  CommonKey.publicProcess (expandedPublishedHash (length := length) M v hv k gap minKey tolerance c)
    (fun p => (restoreTranscript M θ (testTranscript c p.1.1 p.2),p.1.2))

theorem expanded_public_raw_secrecy {n length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (expandedPublishedRawHash (length := length) M θ v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (expandedPublishedRawHash (length := length) M θ v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) :=
  CommonKey.publicProcess_secrecy _ _ _ (expanded_published_secrecy M v hv k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
