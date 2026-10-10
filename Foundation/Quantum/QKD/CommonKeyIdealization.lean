import Foundation.Quantum.QKD.CommonKeyComposition

/-! The explicit common-key ideal equals a fresh uniform replacement of both
classical keys. This is equality of actual operators, with the quantum
conditional blocks retained. -/
namespace Foundation.Quantum.QKD.CommonKey
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {K T : Type} [Fintype K] [Nonempty K] [Fintype T] [DecidableEq K] [DecidableEq T] {e : Space}

def replaceKeys (x : K) (p : (K × K) × T) : (K × K) × T := ((x,x),p.2)

omit [Nonempty K] in
theorem replaceKeys_block (ρ : State ((K × K) × T) e) (x a b : K) (t : T) :
    (relabel ρ (replaceKeys x)).block ((a,b),t) =
      if x = a ∧ x = b then ∑ c, ∑ d, ρ.block ((c,d),t) else 0 := by
  simp [relabel, replaceKeys, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

/-- A fresh uniform key replacement is exactly the common-key ideal. -/
theorem ideal_uniform_replacement (ρ : State ((K × K) × T) e) :
    joint (ideal ρ) = ∑ x : K, ((1/(Fintype.card K:ℝ):ℝ):ℂ) • joint (relabel ρ (replaceKeys x)) := by
  apply Matrix.ext
  intro ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨⟨⟨a,b⟩,t⟩,rfl⟩ := (Fintype.equivFin ((K × K) × T)).surjective r
  obtain ⟨p,rfl⟩ := (Fintype.equivFin ((K × K) × T)).surjective s
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [joint_block (ideal ρ)]
  have hj (x : K) := joint_block (relabel ρ (replaceKeys x)) ((a,b),t) p i j
  simp_rw [hj]
  by_cases h : ((a,b),t) = p
  · subst p
    simp only [ite_true]
    rw [ideal_block]
    have hb (x : K) := replaceKeys_block ρ x a b t
    simp_rw [hb]
    by_cases hab : a = b
    · subst b
      simp only [and_self, Matrix.ite_apply, Matrix.zero_apply, smul_eq_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, uniformize, Matrix.smul_apply]
      simp_rw [aliceView_block]
    · have hn (x : K) : ¬ (x = a ∧ x = b) := by
        rintro ⟨ha,hb⟩
        exact hab (ha.symm.trans hb)
      simp [hab, hn, smul_eq_mul]
  · simp [h]

end
end Foundation.Quantum.QKD.CommonKey
