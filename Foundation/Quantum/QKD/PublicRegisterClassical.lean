import Foundation.Quantum.QKD.PublicRegisterExpose

namespace Foundation.Quantum.QKD.PublicRegisterExpose
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {X Y R : Type} [Fintype X] [Fintype Y] [Fintype R] [DecidableEq R] {e : Space}

theorem withPublic_diagonal (ρ : State (X × R) e) : Diagonal (withPublic ρ) := by
  intro x r s u v
  rw [HashLayout.public_block, HashLayout.public_block]
  simp only [ite_true]

theorem relabel_diagonal [DecidableEq Y] (ρ : State X (Guessing.publicSpace R e))
    (hρ : Diagonal ρ) (f : X → Y) : Diagonal (relabel ρ f) := by
  intro y r s u v
  simp only [relabel, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  have hd (x : X) := hρ x r s u v
  simp_rw [hd]
  by_cases h : r = s <;> simp [h]

theorem seed_diagonal {S : Type} [Fintype S] (p : PMF S)
    (ρ : State X (Guessing.publicSpace R e)) (hρ : Diagonal ρ) : Diagonal (seed p ρ) := by
  intro sx r s u v
  simp only [seed, Matrix.smul_apply, smul_eq_mul]
  rw [hρ]
  by_cases h : r = s <;> simp [h]

theorem hash_output_diagonal {K L S : Type} [Fintype K] [Fintype L] [Fintype S]
    [DecidableEq K] [DecidableEq L] [DecidableEq S]
    (ρ : State (X × L) (Guessing.publicSpace R e)) (hρ : Diagonal ρ)
    (p : PMF S) (h : S → X → K) : Diagonal (HashLayout.output ρ p h) :=
  relabel_diagonal _ (seed_diagonal p ρ hρ) _

end
end Foundation.Quantum.QKD.PublicRegisterExpose
