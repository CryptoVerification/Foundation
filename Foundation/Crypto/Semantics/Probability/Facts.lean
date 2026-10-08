import Foundation.Crypto.Semantics.Probability.Comp

/-! Distribution facts independent of a scheme, tag representation or machine.
Semantic maps do not assert any runtime cost for their host functions. -/
namespace Foundation.Probability
open scoped ENNReal

theorem uniform_map_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [uniform, Fintype.card_congr e]
  · intro a ha
    simp only [ite_eq_right_iff]
    intro h
    exact False.elim (ha (by simpa using congrArg e.symm h.symm))

theorem uniform_pair {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniform α).bind (fun a => (uniform β).map (fun b => (a, b))) = uniform (α × β) := by
  classical
  ext ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, uniform, ENNReal.mul_inv,
    Prod.mk.injEq, ite_and, mul_ite]

theorem uniform_guess {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    eventProb (uniform α) (· = a) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  simp [eventProb, uniform, Set.indicator_apply]

/-- A bound need only hold on branches that have nonzero probability. -/
theorem eventProb_bind_le_of_support {α β : Type*} (p : PMF α) (f : α → PMF β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a ∈ p.support, eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ bound := by
  unfold eventProb
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' a, p a * bound := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · exact mul_le_mul_right (h a ((PMF.mem_support_iff _ _).mpr ha)) (p a)
    _ = bound := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem eventProb_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a, eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ bound :=
  eventProb_bind_le_of_support p f event bound (fun a _ => h a)

end Foundation.Probability
