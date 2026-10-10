import Foundation.Quantum.QKD.DominatedLeak

/-! Positive-block comparison, including event selection and public disclosure.
This order keeps quantum matrices, rather than only their trace weights. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y L : Type} [Fintype X] [Fintype Y] [Fintype L] {e : Space}

def Below (ρ σ : State X e) : Prop := ∀ x, (σ.block x - ρ.block x).PosSemidef

theorem restrict_below (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    Below (restrict ρ P) ρ := by
  intro x
  by_cases hx : P x
  · simp only [restrict, hx, ite_true, sub_self]
    exact Matrix.PosSemidef.zero
  · simpa only [restrict, hx, ite_false, sub_zero] using ρ.positive x

theorem relabel_below [DecidableEq Y] (ρ σ : State X e) (f : X → Y)
    (h : Below ρ σ) : Below (relabel ρ f) (relabel σ f) := by
  intro y
  simp only [relabel, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro x _
  by_cases hx : f x = y
  · simpa only [hx, ite_true] using h x
  · simp only [hx, ite_false, sub_self]
    exact Matrix.PosSemidef.zero

theorem withPublic_below (ρ σ : State (X × L) e) (h : Below ρ σ) :
    Below (withPublic ρ) (withPublic σ) := by
  intro x
  simp only [withPublic, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro l _
  have he : Matrix.kronecker (basisDensity (.register (Fintype.card L)) (Fintype.equivFin L l)).matrix
      (σ.block (x,l) - ρ.block (x,l)) =
      Matrix.kronecker (basisDensity _ (Fintype.equivFin L l)).matrix (σ.block (x,l)) -
      Matrix.kronecker (basisDensity _ (Fintype.equivFin L l)).matrix (ρ.block (x,l)) := by
    ext ⟨r,i⟩ ⟨s,j⟩
    simp [Matrix.kronecker, Matrix.kroneckerMap, mul_sub]
  rw [← he]
  exact (basisDensity _ _).positive.kronecker (h (x,l))

theorem dominated_of_below (ρ σ : State X e) (τ : Density e) (q : ℝ)
    (h : Below ρ σ) (hd : Dominated σ τ q) : Dominated ρ τ q := by
  intro x
  simpa only [sub_add_sub_cancel] using (hd x).add (h x)

end
end Foundation.Quantum.QKD.Subnormalized
