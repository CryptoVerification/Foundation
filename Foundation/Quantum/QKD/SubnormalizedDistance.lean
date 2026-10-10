import Foundation.Quantum.SelectiveDistance
import Foundation.Quantum.QKD.ReadClassicalState
import Foundation.Quantum.Channels

/-! Classical reading, accepted-event selection, and classical output
processing contract distance on the actual joint operators. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type} [Fintype X] [Fintype Y] {e : Space}

theorem readDensity_physical [DecidableEq X]
    (ρ : Density (.tensor (.register (Fintype.card X)) e)) :
    joint (readDensity (X := X) ρ) = ((dephase (.register (Fintype.card X))).amplify e).toKraus.apply ρ.matrix := by
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective s
  rw [joint_block, dephase_amplify_apply]
  simp only [Equiv.apply_eq_iff_eq, readDensity, readCQ, ofCQ, Matrix.submatrix_apply]
  by_cases h : x = y <;> simp [h]

theorem readDensity_approx [DecidableEq X]
    (ρ σ : Density (.tensor (.register (Fintype.card X)) e)) (ε : ℝ) (h : StateApprox ρ σ ε) :
    OperatorApprox (joint (readDensity (X := X) ρ)) (joint (readDensity (X := X) σ)) ε := by
  rw [readDensity_physical, readDensity_physical]
  exact OperatorApprox.postprocess _ h

theorem eventFilter_effect (P : X → Prop) [DecidablePred P] :
    (eventFilter (e := e) P).effect = (recordEvent e (fun t => P ((Fintype.equivFin X).symm t))).matrix := by
  rw [eventFilter, Kraus.single_effect]
  change (Matrix.diagonal (fun i : ((Space.register (Fintype.card X)).tensor e).Basis =>
    if P ((Fintype.equivFin X).symm i.1) then (1:ℂ) else 0)).conjTranspose *
    Matrix.diagonal (fun i => if P ((Fintype.equivFin X).symm i.1) then (1:ℂ) else 0) = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hi : P ((Fintype.equivFin X).symm i.1) <;>
    simp [recordEvent, Matrix.diagonal_apply, hi]


theorem restrict_approx [DecidableEq X] (ρ σ : State X e) (P : X → Prop) [DecidablePred P]
    (ε : ℝ) (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (restrict ρ P)) (joint (restrict σ P)) ε := by
  rw [restrict_physical, restrict_physical]
  apply h.selective
  rw [eventFilter_effect]
  exact (recordEvent e (fun t => P ((Fintype.equivFin X).symm t))).complement_positive

theorem relabel_approx [DecidableEq Y] (ρ σ : State X e) (f : X → Y) (ε : ℝ)
    (h : OperatorApprox (joint ρ) (joint σ) ε) :
    OperatorApprox (joint (relabel ρ f)) (joint (relabel σ f)) ε := by
  rw [relabel_physical, relabel_physical]
  exact h.postprocess _

end
end Foundation.Quantum.QKD.Subnormalized
