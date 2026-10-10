import Foundation.Quantum.ClassicalMap

/-! Composition of deterministic classical processing, with the entire
conditional quantum register retained. Equality is of the interpreted
operations; no equality of Kraus lists or derivation trees is asserted. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Successive physical classical relabellings implement function composition. -/
theorem classicalMap_compose {n m k : Nat} (a : Space) (f : Fin n → Fin m) (g : Fin m → Fin k)
    (ρ : Operator (.tensor (.register n) a)) :
    (classicalMap a g).toKraus.apply ((classicalMap a f).toKraus.apply ρ) =
      (classicalMap a (g ∘ f)).toKraus.apply ρ := by
  change Matrix (Fin n × a.Basis) (Fin n × a.Basis) ℂ at ρ
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [classicalMap_apply, classicalMap_apply]
  have hf (t : Fin m) := classicalMap_apply a f ρ t t i j
  simp only [ite_true] at hf
  simp_rw [hf]
  by_cases hrs : r = s
  · simp only [hrs, ite_true, Function.comp_apply]
    have hdist (x : Fin m) :
        (if g x = s then ∑ t, if f t = x then ρ (t,i) (t,j) else 0 else 0) =
        ∑ t, if f t = x then (if g x = s then ρ (t,i) (t,j) else 0) else 0 := by
      by_cases hx : g x = s <;> simp [hx]
    simp_rw [hdist]
    rw [Finset.sum_comm]
    simp
  · simp only [hrs, ite_false]

end
end Foundation.Quantum
