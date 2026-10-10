import Foundation.Quantum.QKD.PairwiseExpandedVerificationPublicRaw
import Foundation.Quantum.QKD.VerifiedHashProcess

/-! Exact full-position output restoration for the same two independently
seeded checks and hash procedure. Only public labels are changed at this step. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def restoreRecord {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (p : RawProtocol.PublicRecord (BB84SiftedInput.selectedCount M)) : RawProtocol.PublicRecord n :=
  ⟨θ, BB84SiftingRandomness.bobBases θ M, BB84SiftedInput.liftTest M p.tested,
    BB84SiftedInput.expand M p.aliceTest, BB84SiftedInput.expand M p.bobTest, p.accepted⟩

def restoredVerifiedHash {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  VerifiedHash.fixed (length := length)
    (relabel (ofCQ (rawState v hv k gap minKey tolerance c)) (BB84SiftedInput.restoreOutput M θ)) s

theorem restoredVerifiedHash_eq {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    restoredVerifiedHash (length := length) M θ v hv k gap minKey tolerance c s =
      CommonKey.publicProcess (verifiedRawHash (length := length) M v hv k gap minKey tolerance c s)
        (fun p => (((restoreRecord M θ p.1.1.1,p.1.1.2),p.1.2),p.2)) := by
  unfold restoredVerifiedHash VerifiedHash.fixed verifiedRawHash checkedRaw CommonKey.publicProcess
  rw [restrict_relabel, restrict_relabel, seed_relabel, relabel_comp, relabel_comp]
  rfl

theorem restored_verified_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (restoredVerifiedHash (length := length) M θ v hv k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (restoredVerifiedHash (length := length) M θ v hv k gap minKey tolerance c s)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  rw [restoredVerifiedHash_eq]
  exact CommonKey.publicProcess_secrecy _ _ _ (verified_raw_secrecy M v hv k gap minKey tolerance c s)

/-- Both seed distributions are the full original-position distributions. -/
def restoredVerifiedAverage {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  VerifiedHash.average (tag := tag) (length := length)
    (relabel (ofCQ (rawState v hv k gap minKey tolerance c)) (BB84SiftedInput.restoreOutput M θ))

theorem restored_verified_average_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (restoredVerifiedAverage (tag := tag) (length := length) M θ v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (restoredVerifiedAverage (tag := tag) (length := length) M θ v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  have h := CommonKey.mixture_secrecy (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => restoredVerifiedHash (length := length) M θ v hv k gap minKey tolerance c s)
    (fun _ => (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
      ((1-1/Fintype.card (IdealKey.Key length))*
        ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1))))
    (fun s => restored_verified_secrecy M θ v hv k gap minKey tolerance c s)
  simpa only [restoredVerifiedAverage, VerifiedHash.average, restoredVerifiedHash,
    ← Finset.sum_mul, Density.probability_weights, one_mul] using h

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
