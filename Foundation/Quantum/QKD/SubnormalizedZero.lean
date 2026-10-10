import Foundation.Quantum.QKD.CommonKeyMixture

/-! Zero-probability accepted branches, without conditional normalization. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {e : Space}

def zero : State X e where
  block _ := 0
  positive _ := Matrix.PosSemidef.zero
  bounded := by simp

theorem joint_zero : joint (zero : State X e) = 0 := by
  classical
  ext ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨x,rfl⟩ := (Fintype.equivFin X).surjective r
  obtain ⟨y,rfl⟩ := (Fintype.equivFin X).surjective s
  rw [joint_block]
  simp [zero]

theorem seed_zero (p : PMF S) : seed p (zero : State X e) = zero := by
  apply State.ext
  funext sx
  simp [seed, zero]

theorem relabel_zero [DecidableEq Y] (f : X → Y) : relabel (zero : State X e) f = zero := by
  apply State.ext
  funext y
  simp [relabel, zero]

theorem restrict_false (ρ : State X e) (P : X → Prop) [DecidablePred P] (h : ∀ x, ¬ P x) :
    restrict ρ P = zero := by
  apply State.ext
  funext x
  simp [restrict, zero, h x]

end
end Foundation.Quantum.QKD.Subnormalized
