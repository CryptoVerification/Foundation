import Foundation.Quantum.QKD.PairwiseReconciledPrivacy
import Foundation.Quantum.QKD.PairwiseAuxiliaryRecovery
import Foundation.Quantum.QKD.SubnormalizedDiscard
import Foundation.Quantum.QKD.CommonKeyMixture

/-! Keep both seeds public on the actual decoded supported-state experiment,
then remove purification and unmatched signals without removing original Eve.
This is not yet the full raw-state protocol identification and sampling transfer. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def publishedWithSeed {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  CommonKey.publicProcess (published (length := length) M v hv k gap minKey tolerance c s)
    (fun p => (p,s))

def publishedAverage {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => publishedWithSeed (length := length) M v hv k gap minKey tolerance c s)

theorem published_average_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (publishedAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (publishedAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  have h := CommonKey.mixture_secrecy (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => publishedWithSeed (length := length) M v hv k gap minKey tolerance c s)
    (fun _ => privacyError tag length k gap minKey tolerance c)
    (fun s => CommonKey.publicProcess_secrecy _ _ _ (published_secrecy M v hv k gap minKey tolerance c s))
  simpa only [publishedAverage, ← Finset.sum_mul, Density.probability_weights, one_mul] using h

def finishedPublished {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  post (post (publishedAverage (tag := tag) (length := length) M
    (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)
    (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
      (PairwiseRecovery.krausSpace A)))
    (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e)

theorem finished_published_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (finishedPublished (tag := tag) (length := length) A M k gap minKey tolerance c))
      (joint (CommonKey.uniformize (finishedPublished (tag := tag) (length := length) A M k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  apply CommonKey.quantumProcess_secrecy
  apply CommonKey.quantumProcess_secrecy
  exact published_average_secrecy M (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
    k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
