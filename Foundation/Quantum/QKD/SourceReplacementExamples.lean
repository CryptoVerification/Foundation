import Foundation.Quantum.QKD.SourceReplacementLogic

/-! Concrete source replacement with a computational-basis eavesdropper.
Its X outcome leaves genuine Bob/Eve coherence. A mixed-basis, physically
processed closed derivation is interpreted on the same density operators. -/
namespace Foundation.Quantum.QKD.SourceReplacementExamples
noncomputable section
open Foundation.Logic PureProjection
set_option backward.isDefEq.respectTransparency false

def dilation : Op (qubits 1) (.tensor (qubits 1) .bit) :=
  fun i j => if i.1.1 = j.1 ∧ i.2 = j.1 then 1 else 0

theorem isometry : dilation.conjTranspose*dilation = 1 := by
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  change (∑ k : (Fin 2 × Unit) × Fin 2, star (dilation k (i,()))*dilation k (j,())) =
    if (i,()) = (j,()) then 1 else 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  fin_cases i <;> fin_cases j <;> norm_num [dilation]

def attack : BlockAttack 1 .bit := Channel.ofIsometry dilation isometry

theorem attacked_X_entry :
    (attack.jointState (fun _ => .X) (fun _ => 0)).matrix ((0,()),0) ((1,()),1) = 1/2 := by
  change (Kraus.single dilation).apply
    ((Channel.ofIsometry (blockGate 1 (fun _ => .X)) (blockGate_isometry _ _)).run
      (basisDensity (qubits 1) (0,()))).matrix ((0,()),0) ((1,()),1) = _
  rw [SourceReplacement.prepared_matrix, Kraus.single_apply, SourceReplacement.rank_conjugate]
  simp only [rank, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mulVec, dotProduct]
  change (∑ x : Fin 2 × Unit, dilation ((0,()),0) x * blockGate 1 (fun _ => .X) x (0,())) *
    star (∑ x : Fin 2 × Unit, dilation ((1,()),1) x * blockGate 1 (fun _ => .X) x (0,())) = _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_unique]
  norm_num [dilation, blockGate, bitGate,
    hadamard, Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
    Pi.star_apply, starRingEnd_apply, hadamardCoefficient_square]

/-- The full source record has off-diagonal Bob/Eve coherence in an actual branch. -/
theorem record_coherence :
    (BB84Source.record attack (fun _ => .X)).matrix
      (Fintype.equivFin (qubits 1).Basis (0,()),((0,()),0))
      (Fintype.equivFin (qubits 1).Basis (0,()),((1,()),1)) = 1/4 := by
  rw [BB84Source.record_block]
  change (if (0,()) = (0,()) then (1/2:ℂ)^1 *
    (attack.jointState (fun _ => .X) (fun _ => 0)).matrix ((0,()),0) ((1,()),1) else 0) = _
  rw [if_pos rfl, attacked_X_entry]
  norm_num

/-- Alice's outcome remains uniform under the eavesdropper and in either basis. -/
theorem outcome_uniform (θ : Fin 1 → BB84Basis) (x : (qubits 1).Basis) :
    (SourceReplacement.slice (BB84Source.state attack θ).matrix x).trace.re = 1/2 := by
  simpa only [pow_one] using BB84Source.outcome_weight attack θ x

/-- Nonzero source coherence before the adversary acts. -/
theorem source_coherence : (BB84Source.entangled 1).matrix ((0,()),(0,())) ((1,()),(1,())) = 1/2 := by
  norm_num [BB84Source.entangled, SourceReplacement.pair, PureProjection.pure, rank,
    Matrix.vecMulVec_apply, Pi.star_apply, SourceReplacement.pairVector, starRingEnd_apply,
    hadamardCoefficient_square]

def bases (i : Nat) : Fin 1 → BB84Basis := fun _ => if i = 0 then .Z else .X

def channels : Nat → Channel (SourceReplacementLogic.recordSpace 1 .bit) (SourceReplacementLogic.recordSpace 1 .bit) :=
  fun _ => dephase _

/-- Source replacement, a fair mixture of Z and X, and physical dephasing form
one closed finite derivation, interpreted on this concrete eavesdropping attack. -/
theorem interpreted :
    (SourceReplacementLogic.model attack bases channels).Carrier
      (.process 0 (.mixture 2 (Foundation.Probability.uniform (Fin 2)) (fun i => .entangled i.val)),
       .process 0 (.mixture 2 (Foundation.Probability.uniform (Fin 2)) (fun i => .prepared i.val))) :=
  SourceReplacementLogic.sound attack bases channels
    (SourceReplacementLogic.proof 2 0 (Foundation.Probability.uniform (Fin 2)) Fin.val)
    (fun i => Fin.elim0 i)

end
end Foundation.Quantum.QKD.SourceReplacementExamples
