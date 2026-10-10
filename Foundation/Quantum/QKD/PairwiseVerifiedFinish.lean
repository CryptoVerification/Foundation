import Foundation.Quantum.QKD.PairwiseVerifiedRestoration
import Foundation.Quantum.QKD.PairwiseFinishedRaw

/-! Both full-position seeded procedures on the physical supported raw state.
Discard purification and unmatched signals, retaining the original adversary. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def privacyError {m : Nat} (tag length k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration m) : ℝ :=
  (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
    ((1-1/Fintype.card (IdealKey.Key length))*
      ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))

def finishedVerifiedHash {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  VerifiedHash.fixed (length := length) (ofCQ (finishedRawCQ A M θ k gap minKey tolerance c)) s

/-- Two quantum-side partial traces commute with the same restored seeded
procedure. Neither trace removes the original Eve system. -/
theorem finishedVerifiedHash_eq {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    finishedVerifiedHash (length := length) A M θ k gap minKey tolerance c s =
      post (post (restoredVerifiedHash (length := length) M θ (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c s)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
          (PairwiseRecovery.krausSpace A)))
        (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e) := by
  unfold finishedVerifiedHash finishedRawCQ restoredVerifiedHash recoveredRawCQ
  simp only [VerifiedHash.post_fixed, ← post_ofCQ, ofCQ_relabel, post_relabel]

theorem finished_verified_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (finishedVerifiedHash (length := length) A M θ k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (finishedVerifiedHash (length := length) A M θ k gap minKey tolerance c s)))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [finishedVerifiedHash_eq]
  apply CommonKey.quantumProcess_secrecy
  apply CommonKey.quantumProcess_secrecy
  exact restored_verified_secrecy M θ (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
    k gap minKey tolerance c s

def finishedVerifiedAverage {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  VerifiedHash.average (tag := tag) (length := length) (ofCQ (finishedRawCQ A M θ k gap minKey tolerance c))

theorem finished_verified_average_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (finishedVerifiedAverage (tag := tag) (length := length) A M θ k gap minKey tolerance c))
      (joint (CommonKey.uniformize (finishedVerifiedAverage (tag := tag) (length := length) A M θ k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  have h := CommonKey.mixture_secrecy (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => finishedVerifiedHash (length := length) A M θ k gap minKey tolerance c s)
    (fun _ => privacyError tag length k gap minKey tolerance c)
    (fun s => finished_verified_secrecy A M θ k gap minKey tolerance c s)
  simpa only [finishedVerifiedAverage, VerifiedHash.average, finishedVerifiedHash,
    ← Finset.sum_mul, Density.probability_weights, one_mul] using h

theorem finished_verified_physical {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    VerifiedHash.fromDensity (tag := tag) (length := length) (restoredRaw A M η k gap minKey tolerance c) =
      finishedVerifiedAverage (tag := tag) (length := length) A M
        (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap minKey tolerance c := by
  unfold VerifiedHash.fromDensity finishedVerifiedAverage
  rw [readDensity_congr _ (finishedRawCQ A M
    (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap minKey tolerance c).density
    (finishedRawCQ_physical A M η k gap minKey tolerance c).symm, readDensity_CQ]

theorem finished_verified_physical_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox
      (joint (VerifiedHash.fromDensity (tag := tag) (length := length) (restoredRaw A M η k gap minKey tolerance c)))
      (joint (CommonKey.uniformize (VerifiedHash.fromDensity (tag := tag) (length := length)
        (restoredRaw A M η k gap minKey tolerance c))))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [finished_verified_physical]
  exact finished_verified_average_secrecy A M _ k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
