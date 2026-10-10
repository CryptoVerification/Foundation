import Foundation.Quantum.QKD.BB84Attack

/-! Actual preparation and measurement probabilities for a BB84 attack.
This connects amplitude errors to physical density operators and effects. -/
namespace Foundation.Quantum.QKD.BB84Attack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {e : Space}

/-- The transmitted qubit and attacker's environment remain a joint state. -/
def jointChannel (V : BB84Attack e) : Channel .bit (.tensor .bit e) :=
  Channel.ofIsometry V.dilation V.isometry

/-- Bob's output state discards only the environment. -/
def bobChannel (V : BB84Attack e) : Channel .bit .bit :=
  V.jointChannel.seq (discardRight .bit e)

theorem jointChannel_basis (V : BB84Attack e) (b : Fin 2)
    (i j : Fin 2 × e.Basis) :
    (V.jointChannel.run (basisDensity .bit b)).matrix i j =
      V.dilation i b * star (V.dilation j b) := by
  simp [jointChannel, Channel.run, Channel.ofIsometry, Kraus.single_apply,
    basisDensity, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    mul_ite, ite_mul]

theorem bobChannel_basis (V : BB84Attack e) (b i j : Fin 2) :
    (V.bobChannel.run (basisDensity .bit b)).matrix i j =
      ∑ u : e.Basis, V.dilation (i, u) b * star (V.dilation (j, u) b) := by
  change (V.jointChannel.toKraus.seq (discardRight .bit e).toKraus).apply _ i j = _
  rw [Kraus.seq_apply, discardRight_apply]
  apply Finset.sum_congr rfl
  intro u _
  exact V.jointChannel_basis b (i, u) (j, u)

/-- A basis effect reads exactly the corresponding diagonal density entry. -/
theorem basisEffect_probability (a : Space) (r : a.Basis) (ρ : Density a) :
    (basisEffect a r).probability ρ = (ρ.matrix r r).re := by
  simp [Effect.probability, basisEffect, projector, Matrix.trace, Matrix.mul_apply,
    ite_and, ite_mul]

/-- The earlier squared-amplitude error is the probability of Bob's wrong outcome. -/
theorem zError_probability (V : BB84Attack e) (b : Fin 2) :
    (basisEffect .bit (1 - b)).probability (V.bobChannel.run (basisDensity .bit b)) =
      V.zError b := by
  rw [basisEffect_probability, bobChannel_basis]
  change (∑ u : e.Basis, V.dilation (1 - b, u) b * star (V.dilation (1 - b, u) b)).re =
    ∑ u : e.Basis, Complex.normSq (V.dilation (1 - b, u) b)
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact Complex.mul_conj (V.dilation (1 - b, u) b) |> congrArg Complex.re

/-- The finite-dimensional state of the retained environment is its actual reduction.
The matrix formula uses a swap of the retained/discarded index roles. -/
theorem environment_joint_reduction (V : BB84Attack e) (b : Fin 2) (u v : e.Basis) :
    (V.environmentState b).matrix u v =
      ∑ i : Fin 2, (V.jointChannel.run (basisDensity .bit b)).matrix (i, u) (i, v) := by
  simp only [environmentState, environmentMatrix, jointChannel_basis]

end
end Foundation.Quantum.QKD.BB84Attack
