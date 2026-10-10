import Foundation.Quantum.QKD.AcceptedAbortLogic
import Foundation.Quantum.QKD.PrivacyAmplificationExamples

/-! A nonzero abort branch and a nonzero accepted branch retain coherent
quantum side data. Accepted private keys are independent uniform bits: Alice's
secrecy error is zero, but their weighted disagreement is 1/4. -/
namespace Foundation.Quantum.QKD.AcceptedAbortExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic Subnormalized AcceptedAbort
set_option backward.isDefEq.respectTransparency false

abbrev reference : Density .bit := PrivacyAmplificationExamples.reference

theorem key_card : Fintype.card (K 1) = 2 := by
  simp [K, IdealKey.Key, Fintype.card_pi]

def accepted : State (AcceptedLabel Unit 1) .bit where
  block _ := (1/8:ℂ) • reference.matrix
  positive _ := reference.positive.smul (Complex.nonneg_iff.mpr (by norm_num))
  bounded := by
    norm_num [Matrix.trace_smul, reference.normalized, AcceptedLabel, key_card]

def aborted : State Unit .bit where
  block _ := (1/2:ℂ) • reference.matrix
  positive _ := reference.positive.smul (Complex.nonneg_iff.mpr (by norm_num))
  bounded := by norm_num [Matrix.trace_smul, reference.normalized]

theorem accepted_mass : mass accepted = 1/2 := by
  norm_num [mass, accepted, Matrix.trace_smul, reference.normalized, AcceptedLabel, key_card]

theorem aborted_mass : mass aborted = 1/2 := by
  norm_num [mass, aborted, Matrix.trace_smul, reference.normalized]

theorem total_mass : mass accepted + mass aborted = 1 := by
  rw [accepted_mass, aborted_mass]
  norm_num

theorem alice_block (a : K 1) (t : Unit) :
    (CommonKey.aliceView accepted).block (a,t) = (1/4:ℂ) • reference.matrix := by
  rw [CommonKey.aliceView_block]
  simp only [accepted, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, key_card]
  norm_num

theorem alice_uniform : CommonKey.uniformize (CommonKey.aliceView accepted) =
    CommonKey.aliceView accepted := by
  apply State.ext
  funext ⟨a,t⟩
  change ((1/(Fintype.card (K 1):ℝ):ℝ):ℂ) • ∑ k,
    (CommonKey.aliceView accepted).block (k,t) = _
  simp_rw [alice_block]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, key_card]
  norm_num

theorem secrecy : OperatorApprox (joint (CommonKey.aliceView accepted))
    (joint (CommonKey.uniformize (CommonKey.aliceView accepted))) 0 := by
  rw [alice_uniform]
  exact OperatorApprox.refl _

theorem correctness : CommonKey.correctnessError accepted = 1/4 := by
  have hi (a b : K 1) : (if a = b then (0:ℝ) else 1/8) =
      1/8 - if a = b then 1/8 else 0 := by split_ifs <;> norm_num
  unfold CommonKey.correctnessError
  simp only [accepted, Matrix.trace_smul, reference.normalized, smul_eq_mul, mul_one]
  have hz : (1/8:ℂ).re = (1/8:ℝ) := by norm_num
  simp only [hz]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, nsmul_eq_mul, key_card]
  norm_num

def fullState := state accepted aborted total_mass

def proof : Derivation AcceptedAbortLogic.presentation
    (AcceptedAbortLogic.assumptions 0 (1/4) 0) (.secure 0 ((1/4)+0)) :=
  AcceptedAbortLogic.proof 0 (1/4) 0

theorem interpreted : IdealKey.Secure fullState (1/4) := by
  suffices hh : IdealKey.Secure fullState ((1/4)+0) by simpa only [add_zero] using hh
  have h := AcceptedAbortLogic.sound (fun _ => accepted) (fun _ => aborted)
    (fun _ => total_mass) proof
  apply h
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact le_of_eq correctness
  · have hi1 : i = 1 := by omega
    subst i
    exact secrecy

theorem error_lower_bound (ε : ℝ) (h : IdealKey.Secure fullState ε) : 1/4 ≤ ε := by
  have hh := IdealKey.secure_correctness h
  unfold fullState at hh
  rw [correctness_probability accepted aborted total_mass, correctness] at hh
  exact hh

theorem accepted_coherence (p : AcceptedLabel Unit 1) : accepted.block p 0 1 = 1/16 := by
  norm_num [accepted, Matrix.smul_apply, reference, PrivacyAmplificationExamples.reference, prepare_plus_matrix]

theorem aborted_coherence : aborted.block () 0 1 = 1/4 := by
  norm_num [aborted, Matrix.smul_apply, reference, PrivacyAmplificationExamples.reference, prepare_plus_matrix]

end
end Foundation.Quantum.QKD.AcceptedAbortExamples
