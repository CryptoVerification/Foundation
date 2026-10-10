import Foundation.Quantum.QKD.PairwiseAttackSampling
import Foundation.Quantum.QKD.PairwiseSamplingExamples

/-! Two-signal coherent computational-basis copying attack and the exact
pairwise sampling bound. This small finite example is not a secure-key claim. -/
namespace Foundation.Quantum.QKD.PairwiseAttackExamples
noncomputable section
open PureProjection PairwiseAttackSampling
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

theorem copy_isometry : (Op.copy (qubits 2)).conjTranspose * Op.copy (qubits 2) = 1 := by
  change Op.seq (Op.copy (qubits 2)) (Op.dagger (Op.copy (qubits 2))) = Op.ident (qubits 2)
  exact Op.copy_special _

def attack : BlockAttack 2 (qubits 2) := Channel.ofIsometry (Op.copy (qubits 2)) copy_isometry

/-- This is copying of the computational basis, not a cloning axiom for
unknown quantum states; its X-input joint output has nonzero coherence. -/
theorem attacked_X_coherence :
    (attack.jointState (fun _ => .X) (fun _ => 0)).matrix
      ((0,(0,())),(0,(0,()))) ((1,(1,())),(1,(1,()))) = (1/4:ℂ) := by
  change (Kraus.single (Op.copy (qubits 2))).apply
    ((Channel.ofIsometry (blockGate 2 (fun _ => .X)) (blockGate_isometry _ _)).run
      (basisDensity (qubits 2) (0,(0,())))).matrix _ _ = _
  rw [SourceReplacement.prepared_matrix, Kraus.single_apply, SourceReplacement.rank_conjugate]
  simp only [rank, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mulVec, dotProduct]
  change (∑ x : Fin 2 × (Fin 2 × Unit),
    Op.copy (qubits 2) ((0,(0,())),(0,(0,()))) x * blockGate 2 (fun _ => .X) x (0,(0,()))) *
      star (∑ x : Fin 2 × (Fin 2 × Unit),
        Op.copy (qubits 2) ((1,(1,())),(1,(1,()))) x * blockGate 2 (fun _ => .X) x (0,(0,()))) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  have h01 : (((0,(0,())),(0,(0,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((0,(1,())),(0,(1,()))) := by decide
  have h02 : (((0,(0,())),(0,(0,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((1,(0,())),(1,(0,()))) := by decide
  have h03 : (((0,(0,())),(0,(0,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((1,(1,())),(1,(1,()))) := by decide
  have h30 : (((1,(1,())),(1,(1,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((0,(0,())),(0,(0,()))) := by decide
  have h31 : (((1,(1,())),(1,(1,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((0,(1,())),(0,(1,()))) := by decide
  have h32 : (((1,(1,())),(1,(1,()))) : (Space.tensor (qubits 2) (qubits 2)).Basis) ≠ ((1,(0,())),(1,(0,()))) := by decide
  norm_num [Op.copy, Op.basisMap, blockGate, Op.tensor, bitGate, hadamard,
    hadamardCoefficient_square, h01, h02, h03, h30, h31, h32]

/-- The actual attacked fixed-reference state is pure and normalized after
retaining its explicit dilation environment and both unmatched signals. -/
theorem actual_unit : bracket (vector attack Finset.univ) (vector attack Finset.univ) = 1 :=
  unit _ _

theorem approximation :
    OperatorApprox
      (QuantumSampling.real (PairwiseSampling.distribution
        (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1 (by simp [BB84SiftedInput.selectedCount]))
          (vector attack Finset.univ))
      (QuantumSampling.ideal (PairwiseSampling.distribution
        (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1 (by simp [BB84SiftedInput.selectedCount]))
          (PairwiseQuantumSampling.good 1 1) (vector attack Finset.univ)
            (fun _ => PairwiseQuantumSampling.fallback (vector attack Finset.univ) (unit _ _)))
      (Real.sqrt (1/2:ℝ)) := by
  have h := PairwiseAttackSampling.approximation attack (Finset.univ : Finset (Fin 2)) 1 1
    (by simp [BB84SiftedInput.selectedCount])
  have he : PairwiseSampling.errorBound (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1 1 =
      (1/2:ℝ≥0∞) := by
    have hc : BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2)) = 2 := by
      simp [BB84SiftedInput.selectedCount]
    rw [hc]
    exact PairwiseSampling.two_signal_error
  rw [he] at h
  simpa using h

/-- The existing sampling derivation is interpreted with its classical
hypothesis discharged by the actual proved finite-count bound. -/
theorem interpreted :
    (QuantumSamplingLogic.model
      (PairwiseSampling.distribution (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1
        (by simp [BB84SiftedInput.selectedCount]))
      (PairwiseQuantumSampling.good 1 1) (vector attack Finset.univ) (unit _ _)
      (fun _ => PairwiseQuantumSampling.fallback (vector attack Finset.univ) (unit _ _))
      (fun _ => Channel.identity _)).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound
          (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1 1).toReal)) :=
  PairwiseQuantumSampling.interpreted _ _ _ _ _ _

end
end Foundation.Quantum.QKD.PairwiseAttackExamples
