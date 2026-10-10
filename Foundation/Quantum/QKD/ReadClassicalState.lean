import Foundation.Quantum.QKD.SubnormalizedMixture

/-! Read the conditional blocks of an actual state in the original finite
classical label type. No preservation of off-diagonal classical coherence is
asserted; already classical CQ states are recovered exactly. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X S : Type} [Fintype X] [Fintype S] {e : Space}

def readCQ (ρ : Density (.tensor (.register (Fintype.card X)) e)) : Guessing.CQ X e where
  block x := ρ.matrix.submatrix (fun i => (Fintype.equivFin X x,i)) (fun j => (Fintype.equivFin X x,j))
  positive x := ρ.positive.submatrix _
  normalized := by
    change (∑ x, ∑ i : e.Basis, ρ.matrix (Fintype.equivFin X x,i) (Fintype.equivFin X x,i)) = 1
    rw [← (Fintype.equivFin X).symm.sum_comp]
    simpa only [Equiv.apply_symm_apply, Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using ρ.normalized

def readDensity (ρ : Density (.tensor (.register (Fintype.card X)) e)) : State X e := ofCQ (readCQ ρ)

theorem readDensity_CQ [DecidableEq X] (ρ : Guessing.CQ X e) : readDensity ρ.density = ofCQ ρ := by
  apply State.ext
  funext x
  ext i j
  change ρ.density.matrix (Fintype.equivFin X x,i) (Fintype.equivFin X x,j) = ρ.block x i j
  rw [Guessing.CQ.density_block]
  simp

theorem readDensity_congr (ρ σ : Density (.tensor (.register (Fintype.card X)) e))
    (h : ρ.matrix = σ.matrix) : readDensity (X := X) ρ = readDensity σ := by
  apply State.ext
  funext x
  change ρ.matrix.submatrix _ _ = σ.matrix.submatrix _ _
  rw [h]

theorem readDensity_mixture (p : PMF S)
    (ρ : S → Density (.tensor (.register (Fintype.card X)) e)) :
    readDensity (X := X) (Density.mixture p ρ) = mixture p (fun s => readDensity (ρ s)) := by
  apply State.ext
  funext x
  ext i j
  simp only [readDensity, readCQ, ofCQ, mixture, Density.mixture,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]

end
end Foundation.Quantum.QKD.Subnormalized
