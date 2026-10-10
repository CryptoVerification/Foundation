import Foundation.Quantum.QKD.SubnormalizedPublic

/-! Public-message chain bounds for states of trace at most one. These apply
also to accepted branches, including zero acceptance, without renormalization. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open Guessing (Measurement publicSpace readMeasurement)
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X L C : Type} [Fintype X] [Fintype L] [Fintype C] {e : Space}

def hideLeak (ρ : State (X × L) e) : State X e where
  block x := ∑ l, ρ.block (x,l)
  positive x := Matrix.posSemidef_sum _ (fun l _ => ρ.positive (x,l))
  bounded := by
    simp only [Matrix.trace_sum, Complex.re_sum]
    simpa only [Fintype.sum_prod_type] using ρ.bounded

theorem hidden_remainder_positive (ρ : State (X × L) e) (x : X) (l : L) :
    ((hideLeak ρ).block x - ρ.block (x,l)).PosSemidef := by
  classical
  have hp := Matrix.posSemidef_sum (Finset.univ.erase l) (fun k _ => ρ.positive (x,k))
  have heq : (∑ k ∈ Finset.univ.erase l, ρ.block (x,k)) = (∑ k, ρ.block (x,k)) - ρ.block (x,l) := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ l)
  simpa only [heq,hideLeak] using hp

variable [Nonempty X]

omit [Nonempty X] in
theorem leak_branch_le (ρ : State (X × L) e) (M : L → Measurement X e) (l : L) :
    (∑ x, ((M l).operator x * ρ.block (x,l)).trace.re) ≤ probability (hideLeak ρ) := by
  apply le_trans _ (score_le_probability (hideLeak ρ) (M l))
  apply Finset.sum_le_sum
  intro x _
  have hh := (Complex.nonneg_iff.mp
    (trace_product_nonneg ((M l).positive x) (hidden_remainder_positive ρ x l))).1
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hh
  linarith

theorem leakage_chain (ρ : State (X × L) e) :
    probability (withPublic ρ) ≤ Fintype.card L * probability (hideLeak ρ) := by
  apply csSup_le (range_nonempty _)
  intro q hq
  obtain ⟨M,rfl⟩ := hq
  rw [score_withPublic]
  calc
    leakScore ρ (readMeasurement M) ≤ ∑ _ : L, probability (hideLeak ρ) :=
      Finset.sum_le_sum (fun l _ => leak_branch_le ρ _ l)
    _ = _ := by simp

omit [Nonempty X] in
def forgetMessage (ρ : State ((X × C) × L) e) : State (X × L) e where
  block p := ∑ c, ρ.block ((p.1,c),p.2)
  positive p := Matrix.posSemidef_sum _ (fun c _ => ρ.positive ((p.1,c),p.2))
  bounded := by
    simp only [Matrix.trace_sum, Complex.re_sum, Fintype.sum_prod_type]
    have h := ρ.bounded
    simp only [Fintype.sum_prod_type] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]

omit [Nonempty X] in
theorem hide_withPublic (ρ : State ((X × C) × L) e) :
    hideLeak (withPublic ρ) = withPublic (forgetMessage ρ) := by
  apply State.ext
  funext x
  ext ⟨r,i⟩ ⟨s,j⟩
  simp only [hideLeak, withPublic, forgetMessage, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem additional_leakage (ρ : State ((X × C) × L) e) :
    probability (withPublic (withPublic ρ)) ≤
      Fintype.card C * probability (withPublic (forgetMessage ρ)) := by
  simpa only [hide_withPublic] using leakage_chain (withPublic ρ)

end
end Foundation.Quantum.QKD.Subnormalized
