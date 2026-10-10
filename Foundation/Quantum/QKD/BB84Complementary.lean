import Foundation.Quantum.QKD.BB84Basis

/-! Connecting the complementary-basis error to the actual Born probability. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem prepare_plus_matrix (i j : Fin 2) : (prepare .X 0).matrix i j = 1 / 2 := by
  simp only [prepare, basisChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply]
  simp [basisDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, hadamard]
  change hadamardCoefficient * star hadamardCoefficient = _
  rw [hadamardCoefficient_star, hadamardCoefficient_square]
  norm_num

/-- The minus effect is evaluated by an actual Hadamard measurement. -/
theorem minus_probability (ρ : Density .bit) :
    (measurementEffect .X 1).probability ρ =
      ((ρ.matrix 0 0 - ρ.matrix 0 1 - ρ.matrix 1 0 + ρ.matrix 1 1) / 2).re := by
  rw [measurementEffect, ← Effect.probability_run, BB84Attack.basisEffect_probability]
  simp only [basisChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have h10 : hadamard 1 0 = hadamardCoefficient := by simp [hadamard]
  have h11 : hadamard 1 1 = -hadamardCoefficient := by simp [hadamard]
  simp only [h10, h11]
  change ((hadamardCoefficient * ρ.matrix 0 0 + (-hadamardCoefficient) * ρ.matrix 1 0) *
    star hadamardCoefficient +
    (hadamardCoefficient * ρ.matrix 0 1 + (-hadamardCoefficient) * ρ.matrix 1 1) *
    star (-hadamardCoefficient)).re = _
  rw [star_neg, hadamardCoefficient_star]
  congr 1
  linear_combination (ρ.matrix 0 0 - ρ.matrix 0 1 - ρ.matrix 1 0 + ρ.matrix 1 1) *
    hadamardCoefficient_square

namespace BB84Attack
variable {e : Space}

theorem jointChannel_plus (V : BB84Attack e) (i j : Fin 2 × e.Basis) :
    (V.jointChannel.run (prepare .X 0)).matrix i j =
      (V.dilation i 0 + V.dilation i 1) * star (V.dilation j 0 + V.dilation j 1) / 2 := by
  simp only [jointChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, prepare_plus_matrix, Fin.sum_univ_two]
  simp only [star_add]
  ring

theorem bobChannel_plus (V : BB84Attack e) (i j : Fin 2) :
    (V.bobChannel.run (prepare .X 0)).matrix i j =
      ∑ u : e.Basis, (V.dilation (i, u) 0 + V.dilation (i, u) 1) *
        star (V.dilation (j, u) 0 + V.dilation (j, u) 1) / 2 := by
  change (V.jointChannel.toKraus.seq (discardRight .bit e).toKraus).apply _ i j = _
  rw [Kraus.seq_apply, discardRight_apply]
  apply Finset.sum_congr rfl
  intro u _
  exact V.jointChannel_plus (i, u) (j, u)

theorem xPlusError_probability (V : BB84Attack e) :
    (measurementEffect .X 1).probability (V.bobChannel.run (prepare .X 0)) =
      V.xPlusError := by
  rw [minus_probability]
  simp only [bobChannel_plus]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_div, Complex.re_sum]
  change (∑ u : e.Basis, _) = (∑ u : e.Basis, _) / 4
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  have he : ((V.dilation (0, u) 0 + V.dilation (0, u) 1) *
      star (V.dilation (0, u) 0 + V.dilation (0, u) 1) / 2 -
      (V.dilation (0, u) 0 + V.dilation (0, u) 1) *
      star (V.dilation (1, u) 0 + V.dilation (1, u) 1) / 2 -
      (V.dilation (1, u) 0 + V.dilation (1, u) 1) *
      star (V.dilation (0, u) 0 + V.dilation (0, u) 1) / 2 +
      (V.dilation (1, u) 0 + V.dilation (1, u) 1) *
      star (V.dilation (1, u) 0 + V.dilation (1, u) 1) / 2) / 2 =
      (V.dilation (0, u) 0 + V.dilation (0, u) 1 - V.dilation (1, u) 0 - V.dilation (1, u) 1) *
      star (V.dilation (0, u) 0 + V.dilation (0, u) 1 - V.dilation (1, u) 0 - V.dilation (1, u) 1) / 4 := by
    simp only [star_add, star_sub]
    ring
  rw [he]
  let z : ℂ := V.dilation (0, u) 0 + V.dilation (0, u) 1 -
    V.dilation (1, u) 0 - V.dilation (1, u) 1
  change (z * star z / 4).re = Complex.normSq z / 4
  have hz : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  rw [hz]
  simp

/-- Exact nondisturbance is derived from physical measurement probabilities. -/
theorem environment_independent_of_tests (V : BB84Attack e)
    (h0 : (basisEffect .bit 1).probability (V.bobChannel.run (basisDensity .bit 0)) = 0)
    (h1 : (basisEffect .bit 0).probability (V.bobChannel.run (basisDensity .bit 1)) = 0)
    (hx : (measurementEffect .X 1).probability (V.bobChannel.run (prepare .X 0)) = 0)
    (E : Effect e) (b c : Fin 2) :
    E.probability (V.environmentState b) = E.probability (V.environmentState c) := by
  apply V.environment_test_independent
  · apply V.zeroZ_of_errors
    · simpa only [← zError_probability, sub_zero] using h0
    · simpa only [← zError_probability, sub_self] using h1
  · exact V.zeroX_of_error ((V.xPlusError_probability).symm.trans hx)

end BB84Attack
end
end Foundation.Quantum.QKD
