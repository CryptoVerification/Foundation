import Foundation.Quantum.QKD.BB84Vector

/-! A quantitative single-signal BB84 information/disturbance bound. It is
coarse but independent of environment dimension, holds for every binary
effect, and follows from physical error probabilities without zero-error
premises. It is not a finite-key or coherent-many-signal security theorem. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A verified, deliberately non-optimal information/disturbance error bound. -/
def bb84PrivacyError (z0 z1 x : ℝ) : ℝ :=
  4 * Real.sqrt x + 2 * Real.sqrt z0 + 2 * Real.sqrt z1 + z0 + z1

theorem bb84PrivacyError_mono {z0 z1 x t0 t1 y : ℝ}
    (h0 : z0 ≤ t0) (h1 : z1 ≤ t1) (hx : x ≤ y) :
    bb84PrivacyError z0 z1 x ≤ bb84PrivacyError t0 t1 y := by
  unfold bb84PrivacyError
  have hs0 := Real.sqrt_le_sqrt h0
  have hs1 := Real.sqrt_le_sqrt h1
  have hsx := Real.sqrt_le_sqrt hx
  linarith

namespace BB84Attack
variable {e : Space}

theorem environment_weight (V : BB84Attack e) (E : Effect e) (b : Fin 2) :
    E.probability (V.environmentState b) =
      E.weight (V.component 0 b) + E.weight (V.component 1 b) := by
  have he : V.environmentMatrix b =
      Matrix.vecMulVec (WithLp.ofLp (V.component 0 b)) (star (WithLp.ofLp (V.component 0 b))) +
      Matrix.vecMulVec (WithLp.ofLp (V.component 1 b)) (star (WithLp.ofLp (V.component 1 b))) := by
    ext u v
    simp [environmentMatrix, Fin.sum_univ_two, Matrix.vecMulVec, component]
  change (E.matrix * V.environmentMatrix b).trace.re = _
  rw [he, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rfl

/-- All binary measurements of the retained environment have a controlled probability gap. -/
theorem environment_test_bound_zero_one (V : BB84Attack e) (E : Effect e) :
    |E.probability (V.environmentState 0) - E.probability (V.environmentState 1)| ≤
      bb84PrivacyError (V.zError 0) (V.zError 1) V.xPlusError := by
  rw [environment_weight, environment_weight]
  have hB : E.weight (V.component 1 0) ≤ V.zError 0 := by
    simpa [V.zError_norm 0] using E.weight_le_norm_sq (V.component 1 0)
  have hC : E.weight (V.component 0 1) ≤ V.zError 1 := by
    simpa [V.zError_norm 1] using E.weight_le_norm_sq (V.component 0 1)
  have hBC : |E.weight (V.component 1 0) - E.weight (V.component 0 1)| ≤
      V.zError 0 + V.zError 1 := by
    apply abs_le.mpr
    constructor <;> linarith [E.weight_nonneg (V.component 1 0),
      E.weight_nonneg (V.component 0 1)]
  have hAD : |E.weight (V.component 0 0) - E.weight (V.component 1 1)| ≤
      2 * ‖V.component 0 0 - V.component 1 1‖ :=
    (E.weight_sub_bound _ _).trans (mul_le_mul_of_nonneg_right
      (by linarith [V.component_norm_le_one 0 0, V.component_norm_le_one 1 1]) (norm_nonneg _))
  calc
    _ = |(E.weight (V.component 0 0) - E.weight (V.component 1 1)) +
        (E.weight (V.component 1 0) - E.weight (V.component 0 1))| := by congr 1; ring
    _ ≤ |E.weight (V.component 0 0) - E.weight (V.component 1 1)| +
        |E.weight (V.component 1 0) - E.weight (V.component 0 1)| := abs_add_le _ _
    _ ≤ 2 * ‖V.component 0 0 - V.component 1 1‖ + (V.zError 0 + V.zError 1) :=
      add_le_add hAD hBC
    _ ≤ 2 * (2 * Real.sqrt V.xPlusError + Real.sqrt (V.zError 0) +
        Real.sqrt (V.zError 1)) + (V.zError 0 + V.zError 1) :=
      add_le_add (mul_le_mul_of_nonneg_left V.correct_vector_distance (by norm_num)) le_rfl
    _ = _ := by unfold bb84PrivacyError; ring

/-- The bound remains valid after any further physical processing of the environment. -/
theorem environment_postprocess_bound {f : Space} (V : BB84Attack e)
    (C : Channel e f) (E : Effect f) :
    |E.probability (C.run (V.environmentState 0)) -
      E.probability (C.run (V.environmentState 1))| ≤
      bb84PrivacyError (V.zError 0) (V.zError 1) V.xPlusError := by
  rw [Effect.probability_run, Effect.probability_run]
  exact V.environment_test_bound_zero_one (C.pullEffect E)

/-- The hypotheses are upper bounds on measured error rates, not amplitude equations. -/
theorem environment_bound_of_tests (V : BB84Attack e) {z0 z1 x : ℝ}
    (h0 : (basisEffect .bit 1).probability (V.bobChannel.run (basisDensity .bit 0)) ≤ z0)
    (h1 : (basisEffect .bit 0).probability (V.bobChannel.run (basisDensity .bit 1)) ≤ z1)
    (hx : (measurementEffect .X 1).probability (V.bobChannel.run (prepare .X 0)) ≤ x)
    (E : Effect e) :
    |E.probability (V.environmentState 0) - E.probability (V.environmentState 1)| ≤
      bb84PrivacyError z0 z1 x := by
  apply (V.environment_test_bound_zero_one E).trans
  apply bb84PrivacyError_mono
  · simpa only [← zError_probability, sub_zero] using h0
  · simpa only [← zError_probability, sub_self] using h1
  · exact (V.xPlusError_probability).symm.trans_le hx

end BB84Attack
end
end Foundation.Quantum.QKD
