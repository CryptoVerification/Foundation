import Foundation.Quantum.QKD.DominatedLeak
import Foundation.Quantum.QKD.SubnormalizedEquiv

/-! Split a classical key bijectively into a retained key and a disclosed
part. Only the disclosed alphabet costs a factor, with the old side system
retained and no normalization by the accepted mass. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

theorem split_dominated {X R T : Type} [Fintype X] [Fintype R] [Fintype T]
    [DecidableEq R] [DecidableEq T] [Nonempty T] {e : Space}
    (ρ : State X e) (f : X ≃ (R × T)) (τ : Density e) (q : ℝ)
    (hdom : Dominated ρ τ q) :
    Dominated (withPublic (relabel ρ f)) (leakedReference (C := T) τ) (Fintype.card T*q) := by
  intro r
  rw [leakedReference_scaled]
  have hb := ClassicalBlocks.representation (fun t : T => (relabel ρ f).block (r,t))
  change (ClassicalBlocks.of (fun _ : T => (q:ℂ) • τ.matrix) -
    ∑ t, Matrix.kronecker (basisDensity _ (Fintype.equivFin T t)).matrix
      ((relabel ρ f).block (r,t))).PosSemidef
  rw [← hb, ← ClassicalBlocks.sub]
  apply ClassicalBlocks.positive
  intro t
  rw [relabel_equiv_block]
  exact hdom _

end
end Foundation.Quantum.QKD.Subnormalized
