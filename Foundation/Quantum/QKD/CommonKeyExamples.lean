import Foundation.Quantum.QKD.CommonKeyLogic
import Foundation.Quantum.QKD.PrivacyAmplificationExamples

/-! Alice's key is exactly uniform even conditioned on the public error flag,
but Bob's key disagrees with probability 1/4. The full joint ideal bound needs
this correctness term. A coherent quantum auxiliary system is retained. -/
namespace Foundation.Quantum.QKD.CommonKeyExamples
noncomputable section
open scoped ComplexOrder
open Foundation.Logic Subnormalized CommonKey
set_option backward.isDefEq.respectTransparency false

abbrev Label := ((Fin 2 × Fin 2) × Fin 2)
abbrev reference : Density .bit := PrivacyAmplificationExamples.reference

def cq : Guessing.CQ Label .bit where
  block p := if p.2 = (if p.1.1 = p.1.2 then 0 else 1) then
    (if p.1.1 = p.1.2 then (3/8:ℂ) else (1/8:ℂ)) • reference.matrix else 0
  positive p := by
    split_ifs <;> first
      | exact Matrix.PosSemidef.zero
      | exact reference.positive.smul (by apply Complex.nonneg_iff.mpr; norm_num)
  normalized := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace_smul, reference.normalized]

def state : State Label .bit := ofCQ cq

theorem correctness : correctnessError state = 1/4 := by
  norm_num [correctnessError, state, ofCQ, cq, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.trace_smul, reference.normalized]

theorem alice_block (a t : Fin 2) : (aliceView state).block (a,t) =
    (if t = 0 then (3/8:ℂ) else (1/8:ℂ)) • reference.matrix := by
  fin_cases a <;> fin_cases t <;>
    norm_num [aliceView, relabel, state, ofCQ, cq, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem alice_uniform : uniformize (aliceView state) = aliceView state := by
  apply State.ext
  funext ⟨a,t⟩
  change ((1/(Fintype.card (Fin 2):ℝ):ℝ):ℂ) • ∑ k, (aliceView state).block (k,t) = _
  simp_rw [alice_block]
  simp only [Fin.sum_univ_two, ← add_smul, smul_smul]
  fin_cases t <;> norm_num

theorem secrecy : OperatorApprox (joint (aliceView state)) (joint (uniformize (aliceView state))) 0 := by
  rw [alice_uniform]
  exact OperatorApprox.refl _

def proof : Derivation CommonKeyLogic.presentation (CommonKeyLogic.assumptions 0 (1/4) 0)
    (.commonKey 0 (1/4)) := CommonKeyLogic.proof 0 (1/4) 0 (1/4) (by norm_num)

theorem interpreted : OperatorApprox (joint state) (joint (ideal state)) (1/4) := by
  apply CommonKeyLogic.sound (fun _ => state) proof
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact le_of_eq correctness
  · have hi1 : i = 1 := by omega
    subst i
    exact secrecy

theorem error_lower_bound (ε : ℝ)
    (h : OperatorApprox (joint state) (joint (ideal state)) ε) : 1/4 ≤ ε := by
  rw [← correctness]
  exact correctness_le_error state ε h

theorem erroneous_coherence : state.block ((0,1),1) 0 1 = 1/16 := by
  norm_num [state, ofCQ, cq, Matrix.smul_apply, reference, PrivacyAmplificationExamples.reference,
    prepare_plus_matrix]

end
end Foundation.Quantum.QKD.CommonKeyExamples
