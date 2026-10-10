import Foundation.Quantum.QKD.BB84Complementary
import Mathlib.Analysis.Matrix.Order

/-! The exact single-signal BB84 lemma as an actual classical-quantum key state.
The key is uniform and the attack environment is retained. Public transcripts,
abort, sampling and finite-error privacy amplification are separate obligations. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder

/-- Tensor product of two actual normalized density operators. -/
def tensorDensity {a b : Space} (ρ : Density a) (σ : Density b) : Density (.tensor a b) where
  matrix := Matrix.kronecker ρ.matrix σ.matrix
  positive := ρ.positive.kronecker σ.positive
  normalized := by
    unfold Matrix.kronecker
    rw [Matrix.trace_kronecker, ρ.normalized, σ.normalized, mul_one]

/-- The classical key register is an unbiased bit. -/
def uniformBit : Density .bit where
  matrix := (1 / 2 : ℂ) • (1 : Operator .bit)
  positive := Matrix.PosSemidef.one.smul (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by norm_num [Matrix.trace_smul, Matrix.trace_one, Space.Basis]

/-- A uniform classical bit correlated with its two conditional environment states. -/
def keyEnvironment {e : Space} (σ : Fin 2 → Density e) : Density (.tensor .bit e) where
  matrix := (1 / 2 : ℂ) •
    (Matrix.kronecker (basisDensity .bit 0).matrix (σ 0).matrix +
      Matrix.kronecker (basisDensity .bit 1).matrix (σ 1).matrix)
  positive := ((basisDensity .bit 0).positive.kronecker (σ 0).positive).add
    ((basisDensity .bit 1).positive.kronecker (σ 1).positive) |>.smul
      (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by
    simp only [Matrix.kronecker]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_kronecker,
      Matrix.trace_kronecker, (basisDensity .bit 0).normalized,
      (basisDensity .bit 1).normalized, (σ 0).normalized, (σ 1).normalized]
    norm_num

/-- Equality of conditional states implies independence of the entire key register. -/
theorem keyEnvironment_factor {e : Space} (σ : Fin 2 → Density e)
    (h : (σ 0).matrix = (σ 1).matrix) :
    (keyEnvironment σ).matrix = (tensorDensity uniformBit (σ 0)).matrix := by
  ext ⟨i,u⟩ ⟨j,v⟩
  fin_cases i <;> fin_cases j <;>
    simp [keyEnvironment, tensorDensity, uniformBit, basisDensity, Matrix.kronecker,
      Matrix.kroneckerMap, Matrix.diagonal_apply, Matrix.one_apply, ← h]

namespace BB84Attack
variable {e : Space}

/-- Exact secrecy is an equality of a real key-environment state with an independent ideal state. -/
theorem key_state_independent (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX) :
    (keyEnvironment V.environmentState).matrix =
      (tensorDensity uniformBit (V.environmentState 0)).matrix := by
  apply keyEnvironment_factor
  exact V.environment_independent hZ hX 0 1

/-- The exact independent-key conclusion uses physical test probabilities as premises. -/
theorem key_state_independent_of_tests (V : BB84Attack e)
    (h0 : (basisEffect .bit 1).probability (V.bobChannel.run (basisDensity .bit 0)) = 0)
    (h1 : (basisEffect .bit 0).probability (V.bobChannel.run (basisDensity .bit 1)) = 0)
    (hx : (measurementEffect .X 1).probability (V.bobChannel.run (prepare .X 0)) = 0) :
    (keyEnvironment V.environmentState).matrix =
      (tensorDensity uniformBit (V.environmentState 0)).matrix := by
  apply V.key_state_independent
  · apply V.zeroZ_of_errors
    · simpa only [← zError_probability, sub_zero] using h0
    · simpa only [← zError_probability, sub_self] using h1
  · exact V.zeroX_of_error ((V.xPlusError_probability).symm.trans hx)

/-- All joint binary observations of the real and independent key states agree. -/
theorem key_state_test (V : BB84Attack e) (hZ : V.zeroZ) (hX : V.zeroX)
    (E : Effect (.tensor .bit e)) :
    E.probability (keyEnvironment V.environmentState) =
      E.probability (tensorDensity uniformBit (V.environmentState 0)) := by
  unfold Effect.probability
  rw [V.key_state_independent hZ hX]

end BB84Attack
end
end Foundation.Quantum.QKD
