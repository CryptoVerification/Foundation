import Foundation.Quantum.QKD.ReconciledHashProcess
import Foundation.Quantum.QKD.PairwiseAuxiliaryRecovery

/-! The same raw decoding, actual check, public record and two seeds after
removing the proof purification. Direct physical raw-density input, with the
original Eve and unmatched systems retained; no new secrecy assumption. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def recoveredHash {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  ReconciledHash.fixed (length := length) M c.2 (ofCQ (recoveredRawCQ A M k gap minKey tolerance c)) s

theorem recoveredHash_eq {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    recoveredHash (length := length) A M k gap minKey tolerance c s =
      post (rawHash (length := length) M (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
        k gap minKey tolerance c s)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e (PairwiseRecovery.krausSpace A)) := by
  rw [rawHash_process, ReconciledHash.post_fixed, post_ofCQ]
  rfl

theorem recovered_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (recoveredHash (length := length) A M k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (recoveredHash (length := length) A M k gap minKey tolerance c s)))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [recoveredHash_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _ (raw_secrecy M
    (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap minKey tolerance c s)

def recoveredAverage {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  ReconciledHash.average (tag := tag) (length := length) M c.2 (ofCQ (recoveredRawCQ A M k gap minKey tolerance c))

theorem recoveredAverage_eq {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c =
      post (rawAverage (tag := tag) (length := length) M (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e (PairwiseRecovery.krausSpace A)) := by
  rw [rawAverage_process, ReconciledHash.post_average, post_ofCQ]
  rfl

theorem recovered_average_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c))
      (joint (CommonKey.uniformize (recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [recoveredAverage_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _ (raw_average_secrecy M
    (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)

theorem recovered_physical {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    ReconciledHash.fromDensity (tag := tag) (length := length) M c.2 (recoveredRaw A M k gap minKey tolerance c) =
      recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c := by
  unfold ReconciledHash.fromDensity recoveredAverage
  rw [readDensity_congr _ (recoveredRawCQ A M k gap minKey tolerance c).density
    (recoveredRawCQ_physical A M k gap minKey tolerance c).symm, readDensity_CQ]

theorem recovered_physical_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (ReconciledHash.fromDensity (tag := tag) (length := length) M c.2
        (recoveredRaw A M k gap minKey tolerance c)))
      (joint (CommonKey.uniformize (ReconciledHash.fromDensity (tag := tag) (length := length) M c.2
        (recoveredRaw A M k gap minKey tolerance c))))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [recovered_physical]
  exact recovered_average_secrecy A M k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
