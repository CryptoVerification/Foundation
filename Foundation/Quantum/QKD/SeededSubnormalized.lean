import Foundation.Quantum.QKD.SeededCQ

/-! Fresh independent seeds on branches of arbitrary acceptance mass, and
commutation with specified classical processing and selection. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {S X Y : Type} [Fintype S] [Fintype X] [Fintype Y] {e : Space}

theorem seeded_mass (p : PMF S) (B : X → Operator e) :
    (∑ sx : S × X, ((((p sx.1).toReal:ℂ) • B sx.2).trace.re)) =
      ∑ x, (B x).trace.re := by
  simp only [Fintype.sum_prod_type, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum]
  rw [← Finset.sum_mul, Density.probability_weights, one_mul]

def seed (p : PMF S) (ρ : State X e) : State (S × X) e where
  block sx := ((p sx.1).toReal:ℂ) • ρ.block sx.2
  positive sx := (ρ.positive sx.2).smul
    (Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg,by simp⟩)
  bounded := by rw [seeded_mass]; exact ρ.bounded

theorem mass_seed (p : PMF S) (ρ : State X e) : mass (seed p ρ) = mass ρ := seeded_mass p ρ.block

theorem seed_ofCQ (p : PMF S) (ρ : Guessing.CQ X e) :
    seed p (ofCQ ρ) = ofCQ (SeededCQ.independent p ρ) := rfl

theorem seed_restrict (p : PMF S) (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    seed p (restrict ρ P) = restrict (seed p ρ) (fun sx => P sx.2) := by
  apply State.ext
  funext ⟨s,x⟩
  by_cases hx : P x <;> simp [seed, restrict, hx]

theorem seed_relabel [DecidableEq S] [DecidableEq Y] (p : PMF S) (ρ : State X e) (f : X → Y) :
    seed p (relabel ρ f) = relabel (seed p ρ) (fun sx => (sx.1,f sx.2)) := by
  apply State.ext
  funext ⟨s,y⟩
  simp [seed, relabel, Fintype.sum_prod_type, Prod.mk.injEq, ite_and, Finset.smul_sum]

/-- Selection by a property of the output commutes with the stated classical function. -/
theorem restrict_relabel [DecidableEq Y] (ρ : State X e) (f : X → Y)
    (P : Y → Prop) [DecidablePred P] :
    restrict (relabel ρ f) P = relabel (restrict ρ (fun x => P (f x))) f := by
  apply State.ext
  funext y
  simp only [restrict, relabel]
  by_cases hy : P y
  · simp only [hy, ite_true]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxy : f x = y <;> simp [hxy, hy]
  · simp only [hy, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxy : f x = y <;> simp [hxy, hy]

end
end Foundation.Quantum.QKD.Subnormalized
