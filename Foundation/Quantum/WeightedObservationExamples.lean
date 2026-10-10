import Foundation.Quantum.OperatorDistanceLogic
import Foundation.Quantum.QKD.BB84Complementary
import Foundation.Quantum.Channels

/-! A tight coherent-qubit observation bound. The pure X0 state differs from
the maximally mixed state by off-diagonal entries 1/2. The reconstruction and
square certificate are proved, not postulated; a binary measurement attains
the error 1/2. Dephasing removes the difference as an actual operation. -/
namespace Foundation.Quantum.WeightedObservationExamples
noncomputable section
open QKD
open scoped ComplexOrder
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

def mixed : Density .bit where
  matrix := (1/2:ℂ) • 1
  positive := Matrix.PosSemidef.one.smul (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by norm_num [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two]

def pure : Density .bit := prepare .X 0

def delta : Operator .bit := pure.matrix - mixed.matrix

theorem delta_hermitian : delta.IsHermitian := pure.positive.isHermitian.sub mixed.positive.isHermitian

theorem delta_entry (i j : Fin 2) : delta i j = if i = j then 0 else 1/2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [delta, pure, mixed, Matrix.sub_apply, prepare_plus_matrix, Matrix.smul_apply, Matrix.one_apply]

theorem square_value : OperatorDistanceLogic.square delta 1 = 1 := by
  norm_num [OperatorDistanceLogic.square, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_one, Matrix.one_apply, Fin.sum_univ_two, delta_entry]

theorem close : StateApprox pure mixed (1/2) := by
  have h := stateApprox_of_factor pure mixed delta 1 delta_hermitian (by simp [delta])
  change StateApprox pure mixed ((1/2:ℝ)*Real.sqrt (OperatorDistanceLogic.square delta 1)) at h
  simpa only [square_value, Real.sqrt_one, mul_one] using h

theorem measurement_matrix : (measurementEffect .X 0).matrix = pure.matrix := by
  simp only [measurementEffect, basisChannel, Channel.pullEffect, Kraus.dual, Channel.ofIsometry,
    Kraus.single, Finset.univ_unique, Finset.sum_singleton, pure, prepare, Channel.run]
  change hadamard.conjTranspose * (basisEffect .bit 0).matrix * hadamard =
    (Kraus.single hadamard).apply (basisDensity .bit 0).matrix
  rw [Kraus.single_apply, hadamard_adjoint]
  have hb : (basisEffect .bit 0).matrix = (basisDensity .bit 0).matrix := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basisEffect, projector, basisDensity]
  rw [hb]

theorem observed_gap : (measurementEffect .X 0).probability pure -
    (measurementEffect .X 0).probability mixed = 1/2 := by
  have h := matched_basis_correct .X 0
  change (measurementEffect .X 0).probability pure = 1 at h
  rw [h]
  unfold Effect.probability
  rw [measurement_matrix]
  norm_num [mixed, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, pure.normalized]

/-- The 1/2 observation upper bound cannot be reduced in this concrete model. -/
theorem error_lower_bound {ε : ℝ} (h : StateApprox pure mixed ε) : 1/2 ≤ ε := by
  have hh := h (measurementEffect .X 0)
  rw [observed_gap] at hh
  norm_num at hh ⊢
  exact hh

def operators (i : Nat) : Operator .bit := if i = 0 then pure.matrix else mixed.matrix

def proof : Derivation OperatorDistanceLogic.presentation
    (OperatorDistanceLogic.assumptions (.state 0) (.state 1) 0 1)
    (.approx (.process 0 (.state 1)) (.process 0 (.state 0)) ((1/2:ℝ)*Real.sqrt 1)) :=
  OperatorDistanceLogic.weightedPostSymm (.state 0) (.state 1) 0 0 1

theorem interpreted : OperatorApprox ((dephase .bit).toKraus.apply mixed.matrix)
    ((dephase .bit).toKraus.apply pure.matrix) (1/2) := by
  have h := OperatorDistanceLogic.sound operators (fun _ => dephase .bit) (fun _ => delta) (fun _ => 1) proof
  apply (show ((1/2:ℝ)*Real.sqrt 1) = 1/2 by norm_num) ▸ h
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    change delta.IsHermitian ∧ pure.matrix-mixed.matrix = (1:Operator .bit).conjTranspose*delta*1 ∧
      pure.matrix.trace = mixed.matrix.trace
    exact ⟨delta_hermitian,by simp [delta],pure.normalized.trans mixed.normalized.symm⟩
  · have hi1 : i = 1 := by omega
    subst i
    change OperatorDistanceLogic.square delta 1 ≤ 1
    exact le_of_eq square_value

theorem dephase_equal : (dephase .bit).toKraus.apply pure.matrix = (dephase .bit).toKraus.apply mixed.matrix := by
  change (∑ r : Fin 2, projector .bit r * pure.matrix * (projector .bit r).conjTranspose) =
    (∑ r : Fin 2, projector .bit r * mixed.matrix * (projector .bit r).conjTranspose)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.sum_apply, Kraus.apply, projector, Matrix.mul_apply, pure, mixed,
      prepare_plus_matrix, Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Fin.sum_univ_two]

end
end Foundation.Quantum.WeightedObservationExamples
