import Foundation.Quantum.QKD.BB84ErrorLogic
import Foundation.Quantum.QKD.BB84Examples

/-! A nonzero-disturbance attack with a genuinely nontrivial verified error
bound. The numerical parameters are our example, not a claim from the thesis. -/
namespace Foundation.Quantum.QKD.BB84WeakAttack
noncomputable section
set_option backward.isDefEq.respectTransparency false

def dilation (c s : ℝ) : Op .bit (.tensor .bit .bit) := fun i j =>
  if i.1 = j then
    if j = 0 then (if i.2 = 0 then 1 else 0)
    else (if i.2 = 0 then (c : ℂ) else (s : ℂ))
  else 0

theorem dilation_isometry (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (dilation c s).conjTranspose * dilation c s = 1 := by
  ext i j
  change (∑ k : Fin 2 × Fin 2, star (dilation c s k i) * dilation c s k j) =
    if i = j then 1 else 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [dilation, Complex.ext_iff]; nlinarith

/-- Rational parameters keep the example exact, with error probability 1/401. -/
def attack : BB84Attack .bit :=
  ⟨dilation (399 / 401) (40 / 401), dilation_isometry _ _ (by norm_num)⟩

theorem zError (b : Fin 2) : attack.zError b = 0 := by
  fin_cases b <;> norm_num [BB84Attack.zError, attack, dilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype]

theorem xPlusError : attack.xPlusError = 1 / 401 := by
  norm_num [BB84Attack.xPlusError, attack, dilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype, Complex.normSq]

/-- The environment is measurably correlated with the key despite zero Z error. -/
theorem leakage_positive :
    (basisEffect .bit 1).probability (attack.environmentState 1) -
      (basisEffect .bit 1).probability (attack.environmentState 0) = (40 / 401 : ℝ) ^ 2 := by
  rw [BB84Attack.basisEffect_probability, BB84Attack.basisEffect_probability]
  norm_num [BB84Attack.environmentState, BB84Attack.environmentMatrix, attack, dilation,
    Fin.sum_univ_two]
  norm_num [starRingEnd_apply]

/-- Unlike the vacuous bound 1, the quantitative error here is strictly smaller than 1. -/
theorem privacyError_lt_one : bb84PrivacyError 0 0 (1 / 401) < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 401 by norm_num)
  have hn := Real.sqrt_nonneg (1 / 401 : ℝ)
  simp only [bb84PrivacyError, Real.sqrt_zero, mul_zero, add_zero]
  nlinarith

theorem test_hypotheses : ∀ i,
    (BB84ErrorLogic.model (fun _ => attack) (fun _ => dephase .bit)).Carrier
      ((BB84ErrorLogic.testContext 0 0 0 (1 / 401)).claim i) := by
  intro i
  fin_cases i
  · change (basisEffect .bit 1).probability (attack.bobChannel.run (basisDensity .bit 0)) ≤ 0
    simpa only [← BB84Attack.zError_probability, sub_zero] using le_of_eq (zError 0)
  · change (basisEffect .bit 0).probability (attack.bobChannel.run (basisDensity .bit 1)) ≤ 0
    simpa only [← BB84Attack.zError_probability, sub_self] using le_of_eq (zError 1)
  · exact le_of_eq ((attack.xPlusError_probability).trans xPlusError)

/-- The finite-error syntactic proof is interpreted with a real attack and postprocessing. -/
theorem processed_proof_interpreted :
    (BB84ErrorLogic.model (fun _ => attack) (fun _ => dephase .bit)).Carrier
      (.leakage 0 (.seq .identity (.variable 0)) (bb84PrivacyError 0 0 (1 / 401))) :=
  BB84ErrorLogic.sound (fun _ => attack) (fun _ => dephase .bit)
    (BB84ErrorLogic.processedProof 0 0 0 (1 / 401) (.variable 0)) test_hypotheses

end
end Foundation.Quantum.QKD.BB84WeakAttack
