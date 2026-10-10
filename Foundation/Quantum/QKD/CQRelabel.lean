import Foundation.Quantum.QKD.CQRepresentation
import Foundation.Quantum.QKD.GuessLeakage

/-! Deterministic classical processing of CQ states is the existing physical
classical channel. Positive blocks with the same output label are summed;
quantum side information is retained, without conditioning on nonzero events. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type} [Fintype X] [Fintype Y] {e : Space}

@[ext] theorem CQ.ext {ρ σ : CQ X e} (h : ρ.block = σ.block) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Sum the conditional quantum blocks over each classical fiber. -/
def relabel [DecidableEq Y] (ρ : CQ X e) (f : X → Y) : CQ Y e where
  block y := ∑ x, if f x = y then ρ.block x else 0
  positive y := Matrix.posSemidef_sum _ (fun x _ => by
    split_ifs
    · exact ρ.positive x
    · exact Matrix.PosSemidef.zero)
  normalized := by
    simp only [Matrix.trace_sum, apply_ite, Matrix.trace_zero]
    rw [Finset.sum_comm]
    simpa using ρ.normalized

/-- Relabelling is a verified channel on the actual joint density, including
all quantum matrix entries, not just probabilities of classical events. -/
theorem relabel_physical [DecidableEq Y] (ρ : CQ X e) (f : X → Y) :
    (relabel ρ f).density.matrix =
      ((classicalMap e (fun t => Fintype.equivFin Y (f ((Fintype.equivFin X).symm t)))).run ρ.density).matrix := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨y,rfl⟩ := (Fintype.equivFin Y).surjective r
  obtain ⟨z,rfl⟩ := (Fintype.equivFin Y).surjective s
  rw [CQ.density_block]
  change _ = (classicalMap e _).toKraus.apply _ _ _
  rw [classicalMap_apply]
  rw [← (Fintype.equivFin X).sum_comp]
  simp only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]
  by_cases h : y = z
  · subst z
    simp only [ite_true, relabel, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f x = y
    · simp only [hx, ite_true]
      rw [CQ.density_block]
      simp
    · simp [hx]
  · simp [h]

/-- Reading classical blocks commutes with a physical classical function,
even when the original register had off-diagonal coherence. -/
theorem read_relabel_physical {n : Nat} [DecidableEq Y]
    (ρ : Density (.tensor (.register n) e)) (f : Fin n → Y) :
    (relabel (ofDensity ρ) f).density.matrix =
      ((classicalMap e (fun t => Fintype.equivFin Y (f t))).run ρ).matrix := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨y,rfl⟩ := (Fintype.equivFin Y).surjective r
  obtain ⟨z,rfl⟩ := (Fintype.equivFin Y).surjective s
  rw [CQ.density_block]
  change _ = (classicalMap e _).toKraus.apply _ _ _
  rw [classicalMap_apply]
  simp only [Equiv.apply_eq_iff_eq]
  by_cases h : y = z
  · subst z
    simp only [ite_true, relabel, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f x = y <;> simp [hx, ofDensity]
  · simp [h]

/-- Summing over one public component agrees with forgetting that component. -/
theorem relabel_fst [DecidableEq X] (ρ : CQ (X × Y) e) :
    relabel ρ Prod.fst = hideLeak ρ := by
  apply CQ.ext
  funext x
  simp only [relabel, hideLeak, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

end
end Foundation.Quantum.QKD.Guessing
