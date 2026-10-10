import Foundation.Quantum.QKD.PrivacyAmplificationLogic
import Foundation.Quantum.QKD.DominatedCollisionExamples

/-! A coherent rank-one reference is singular, so the faithful-reference
bound cannot be used directly. The finite derivation uses the general rule
whose soundness is proved by regularization and a scalar limit. -/
namespace Foundation.Quantum.QKD.PrivacyAmplificationExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic Collision Hashing
open DominatedCollisionExamples (Input Output Seeds collision_bound)
set_option backward.isDefEq.respectTransparency false

def reference : Density .bit := prepare .X 0

def cq : Guessing.CQ Input .bit where
  block _ := (1/4:ℂ) • reference.matrix
  positive _ := reference.positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by
    simp only [Matrix.trace_smul, reference.normalized, smul_eq_mul, mul_one]
    norm_num [Fintype.card_fun, ZMod.card]

def state : Subnormalized.State Input .bit := Subnormalized.ofCQ cq

theorem reference_singular : ¬IsUnit reference.matrix := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  norm_num [reference, Matrix.det_fin_two, prepare_plus_matrix]

theorem reference_coherence : reference.matrix 0 1 = 1/2 := prepare_plus_matrix 0 1

theorem state_coherence (x : Input) : state.block x 0 1 = 1/8 := by
  norm_num [state, Subnormalized.ofCQ, cq, Matrix.smul_apply, reference, prepare_plus_matrix]

theorem domination : Subnormalized.Dominated state reference (1/4) := by
  intro x
  change (((1/4:ℝ):ℂ) • reference.matrix - (1/4:ℂ) • reference.matrix).PosSemidef
  norm_num
  exact Matrix.PosSemidef.zero

def proof : Derivation (PrivacyAmplificationLogic.presentation 2)
    (PrivacyAmplificationLogic.assumptions 2 0 0 (1/4) 1) (.distance 0 (1/4)) :=
  PrivacyAmplificationLogic.proof 2 0 0 (1/4) 1 (1/4) (by norm_num) (by
    have hs : Real.sqrt (4:ℝ) = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    norm_num [Real.sqrt_div, hs])

theorem interpreted :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform Seeds) (fun s => hashed state.block (linearHash s)))
      (publicMixture (Foundation.Probability.uniform Seeds) (fun _ => uniformComparator (Y := Output) state.block))
      (1/4) := by
  apply PrivacyAmplificationLogic.sound (Foundation.Probability.uniform Seeds) linearHash
    (fun _ => state) (fun _ => reference) collision_bound proof
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact domination
  · have hi1 : i = 1 := by omega
    subst i
    change Subnormalized.mass (Subnormalized.ofCQ cq) ≤ 1
    rw [Subnormalized.mass_ofCQ]

def realOperator := publicMixture (Foundation.Probability.uniform Seeds) (fun s => hashed state.block (linearHash s))
def idealOperator := publicMixture (Foundation.Probability.uniform Seeds) (fun _ => uniformComparator (Y := Output) state.block)

theorem real_entry : realOperator
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0))
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0)) = 0 := by
  unfold realOperator
  rw [publicMixture_block]
  simp only [ite_true, hashed]
  rw [ClassicalBlocks.encoded]
  simp [grouped, linearHash]

theorem ideal_entry : idealOperator
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0))
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0)) = 1/16 := by
  unfold idealOperator
  rw [publicMixture_block]
  simp only [ite_true, uniformComparator]
  rw [ClassicalBlocks.encoded]
  have hc : Fintype.card Seeds = 4 := by
    change Fintype.card (Fin 1 → Fin 2 → ZMod 2) = 4
    norm_num [Fintype.card_fun, ZMod.card]
  have ho : Fintype.card Output = 2 := by norm_num [Fintype.card_fun, ZMod.card]
  have hs : (∑ x : Input, state.block x) 0 0 = 1/2 := by
    rw [Matrix.sum_apply]
    have hv (x : Input) : state.block x 0 0 = 1/8 := by
      norm_num [state, Subnormalized.ofCQ, cq, Matrix.smul_apply, reference, prepare_plus_matrix]
    simp_rw [hv]
    norm_num [Fintype.card_fun, ZMod.card]
  simp only [ite_true, Matrix.smul_apply, smul_eq_mul, hs, ho, Nat.cast_ofNat]
  norm_num [Foundation.Probability.uniform, PMF.uniformOfFintype_apply, hc]

theorem actual_ne_ideal : realOperator ≠ idealOperator := by
  intro h
  have hh := congrFun (congrFun h
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0)))
    (Fintype.equivFin Seeds (0:Seeds),(Fintype.equivFin Output (1:Output),0))
  rw [real_entry, ideal_entry] at hh
  norm_num at hh

end
end Foundation.Quantum.QKD.PrivacyAmplificationExamples
