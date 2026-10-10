import Foundation.Quantum.QKD.ClassicalCoupling

/-! Fresh classical randomness sampled independently of an already fixed
quantum input. Reading and relabelling the resulting blocks equals the actual
mixture of classical channels on the original joint density. -/
namespace Foundation.Quantum.QKD.SeededCQ
noncomputable section
open scoped ComplexOrder
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {S X Y : Type} [Fintype S] [Fintype X] [Fintype Y] {e : Space}

/-- The seed is chosen after the input state; no seed-dependent input is used. -/
def independent (p : PMF S) (ρ : Guessing.CQ X e) : Guessing.CQ (S × X) e where
  block sx := ((p sx.1).toReal:ℂ) • ρ.block sx.2
  positive sx := (ρ.positive sx.2).smul
    (Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg,by simp⟩)
  normalized := by
    simp only [Fintype.sum_prod_type, Matrix.trace_smul, ← Finset.mul_sum,
      ρ.normalized, smul_eq_mul, mul_one, ← Complex.ofReal_sum, Density.probability_weights]
    rfl

/-- The whole conditional quantum matrix is retained for every seed. -/
theorem relabel_independent [DecidableEq Y] (p : PMF S) (ρ : Guessing.CQ X e) (f : S × X → Y) :
    joint (relabel (ofCQ (independent p ρ)) f) =
      ∑ s, ((p s).toReal:ℂ) • joint (relabel (ofCQ ρ) (fun x => f (s,x))) := by
  apply Matrix.ext
  intro ⟨r,i⟩ ⟨t,j⟩
  obtain ⟨y,rfl⟩ := (Fintype.equivFin Y).surjective r
  obtain ⟨z,rfl⟩ := (Fintype.equivFin Y).surjective t
  rw [joint_block (relabel (ofCQ (independent p ρ)) f) y z i j]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hb (s : S) := joint_block (relabel (ofCQ ρ) (fun x => f (s,x))) y z i j
  simp_rw [hb]
  by_cases h : y = z
  · subst z
    simp only [ite_true, relabel, ofCQ, independent, Fintype.sum_prod_type,
      Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      Finset.mul_sum, mul_ite, mul_zero]
  · simp [h]

/-- A physical output channel already reads classical diagonals, even if the
input register had coherence. This equality introduces no assumption about it. -/
theorem physical {m : Nat} [DecidableEq Y] (p : PMF S)
    (ρ : Density (.tensor (.register m) e)) (f : S × Fin m → Y) :
    joint (relabel (ofCQ (independent p (Guessing.ofDensity ρ))) f) =
      (Density.mixture p (fun s => (classicalMap e (fun r => Fintype.equivFin Y (f (s,r)))).run ρ)).matrix := by
  rw [relabel_independent]
  change (∑ s, ((p s).toReal:ℂ) • joint (relabel (ofCQ (Guessing.ofDensity ρ)) (fun r => f (s,r)))) = _
  have hp (s : S) : joint (relabel (ofCQ (Guessing.ofDensity ρ)) (fun r => f (s,r))) =
      ((classicalMap e (fun r => Fintype.equivFin Y (f (s,r)))).run ρ).matrix :=
    Guessing.read_relabel_physical ρ (fun r => f (s,r))
  simp_rw [hp]
  rfl

end
end Foundation.Quantum.QKD.SeededCQ
