import Foundation.Quantum.RecordObservation
import Mathlib.GroupTheory.Index

/-! Uniform fibers of a surjective finite additive homomorphism. This
counting lemma supplies the exact collision probability of linear hashing;
no security premise or quantum entropy assumption is used. -/
namespace Foundation.Quantum.QKD.Hashing
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Every output of a surjective additive homomorphism has the same uniform probability. -/
theorem uniform_hom_fiber {G H : Type} [AddGroup G] [Fintype G]
    [AddGroup H] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (eventProb (uniform G) (fun x => f x = y)).toReal = 1 / Fintype.card H := by
  classical
  let k := (Finset.univ.filter (fun x : G => f x = y)).card
  have hconst (z : H) : (Finset.univ.filter (fun x : G => f x = z)).card = k :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have hcard : Fintype.card G = Fintype.card H * k := by
    have hh := Finset.card_eq_sum_card_fiberwise (f := f) (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ, hconst, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using hh
  obtain ⟨g,hg⟩ := hf y
  have hk : k ≠ 0 := Finset.card_ne_zero.mpr ⟨g, by simp [hg]⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard' : (Fintype.card G : ℝ) = Fintype.card H * (k : ℝ) := by exact_mod_cast hcard
  change ((PMF.uniformOfFintype G).toOuterMeasure {x | f x = y}).toReal = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_subtype]
  change (k : ℝ) / Fintype.card G = _
  rw [hcard']
  field_simp

end
end Foundation.Quantum.QKD.Hashing
