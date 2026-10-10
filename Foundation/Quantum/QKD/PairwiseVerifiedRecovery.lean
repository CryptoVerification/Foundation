import Foundation.Quantum.QKD.VerifiedHashProcess
import Foundation.Quantum.QKD.PairwiseAuxiliaryRecovery

/-! Remove the proof purification's Kraus label after the actual raw check
and PA. Original Eve and unmatched signal systems remain; every public field
and both independently sampled public seeds are unchanged. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def recoveredVerifiedHash {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed (BB84SiftedInput.selectedCount M) tag) :=
  VerifiedHash.fixed (length := length) (ofCQ (recoveredRawCQ A M k gap minKey tolerance c)) s

theorem recoveredVerifiedHash_eq {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed (BB84SiftedInput.selectedCount M) tag) :
    recoveredVerifiedHash (length := length) A M k gap minKey tolerance c s =
      post (verifiedRawHash (length := length) (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c s)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
          (PairwiseRecovery.krausSpace A)) := by
  rw [verifiedRawHash_process, VerifiedHash.post_fixed, post_ofCQ]
  rfl

theorem recovered_verified_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed (BB84SiftedInput.selectedCount M) tag) :
    OperatorApprox (joint (recoveredVerifiedHash (length := length) A M k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (recoveredVerifiedHash (length := length) A M k gap minKey tolerance c s)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  rw [recoveredVerifiedHash_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _
    (verified_raw_secrecy (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
      k gap minKey tolerance c s)

def recoveredVerifiedAverage {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  VerifiedHash.average (tag := tag) (length := length) (ofCQ (recoveredRawCQ A M k gap minKey tolerance c))

theorem recoveredVerifiedAverage_eq {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    recoveredVerifiedAverage (tag := tag) (length := length) A M k gap minKey tolerance c =
      post (verifiedRawAverage (tag := tag) (length := length) (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
          (PairwiseRecovery.krausSpace A)) := by
  rw [verifiedRawAverage_process, VerifiedHash.post_average, post_ofCQ]
  rfl

theorem recovered_verified_average_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (recoveredVerifiedAverage (tag := tag) (length := length) A M k gap minKey tolerance c))
      (joint (CommonKey.uniformize (recoveredVerifiedAverage (tag := tag) (length := length) A M k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  rw [recoveredVerifiedAverage_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _
    (verified_raw_average_secrecy (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
      k gap minKey tolerance c)

/-- The physical recovered raw density, read and processed directly, gives
the same state as the recovered conditional-block construction. -/
theorem recovered_verified_physical {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    VerifiedHash.fromDensity (tag := tag) (length := length) (recoveredRaw A M k gap minKey tolerance c) =
      recoveredVerifiedAverage (tag := tag) (length := length) A M k gap minKey tolerance c := by
  unfold VerifiedHash.fromDensity recoveredVerifiedAverage
  rw [readDensity_congr _ (recoveredRawCQ A M k gap minKey tolerance c).density
    (recoveredRawCQ_physical A M k gap minKey tolerance c).symm, readDensity_CQ]

theorem recovered_verified_physical_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox
      (joint (VerifiedHash.fromDensity (tag := tag) (length := length) (recoveredRaw A M k gap minKey tolerance c)))
      (joint (CommonKey.uniformize (VerifiedHash.fromDensity (tag := tag) (length := length)
        (recoveredRaw A M k gap minKey tolerance c))))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  rw [recovered_verified_physical]
  exact recovered_verified_average_secrecy A M k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
