import Foundation.Quantum.QKD.SubnormalizedLeak

/-! Trace-preserving classical processing of subnormalized states, including
additional public messages on accepted branches. Actual quantum side information
and the branch weight are preserved, with no conditional normalization. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y C L : Type} [Fintype X] [Fintype Y] [Fintype C] [Fintype L] {e : Space}

def relabel [DecidableEq Y] (ρ : State X e) (f : X → Y) : State Y e where
  block y := ∑ x, if f x = y then ρ.block x else 0
  positive y := Matrix.posSemidef_sum _ (fun x _ => by
    split_ifs
    · exact ρ.positive x
    · exact Matrix.PosSemidef.zero)
  bounded := by
    simp only [Matrix.trace_sum, Complex.re_sum, apply_ite, Matrix.trace_zero, Complex.zero_re]
    rw [Finset.sum_comm]
    simpa using ρ.bounded

theorem mass_relabel [DecidableEq Y] (ρ : State X e) (f : X → Y) : mass (relabel ρ f) = mass ρ := by
  simp only [mass, relabel, Matrix.trace_sum, Complex.re_sum, apply_ite,
    Matrix.trace_zero, Complex.zero_re]
  rw [Finset.sum_comm]
  simp

theorem relabel_physical [DecidableEq Y] (ρ : State X e) (f : X → Y) :
    joint (relabel ρ f) = (classicalMap e (fun t => Fintype.equivFin Y
      (f ((Fintype.equivFin X).symm t)))).toKraus.apply (joint ρ) := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨y,rfl⟩ := (Fintype.equivFin Y).surjective r
  obtain ⟨z,rfl⟩ := (Fintype.equivFin Y).surjective s
  rw [joint_block, classicalMap_apply, ← (Fintype.equivFin X).sum_comp]
  simp only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  by_cases h : y = z
  · subst z
    simp only [ite_true, relabel, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f x = y
    · simp only [hx, ite_true]
      rw [joint_block]
      simp
    · simp [hx]
  · simp [h]

def disclose [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C) : State ((X × C) × L) e :=
  relabel ρ (fun p => ((p.1,message p.1 p.2),p.2))

theorem forget_disclose [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C) : forgetMessage (disclose ρ message) = ρ := by
  apply State.ext
  funext ⟨x,l⟩
  simp only [forgetMessage, disclose, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp
  rw [Finset.sum_comm]
  simp

theorem disclosure_cost [Nonempty X] [DecidableEq X] [DecidableEq C] [DecidableEq L]
    (ρ : State (X × L) e) (message : X → L → C) :
    probability (withPublic (withPublic (disclose ρ message))) ≤
      Fintype.card C * probability (withPublic ρ) := by
  simpa only [forget_disclose] using additional_leakage (disclose ρ message)

end
end Foundation.Quantum.QKD.Subnormalized
