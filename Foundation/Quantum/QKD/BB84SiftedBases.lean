import Foundation.Quantum.QKD.BB84SiftedGates

/-! Conditional on the public match set, the selected common bases remain
uniform and independent of the unmatched bases. This identity is transported
through the actual source/attack/raw-record experiment, with all quantum
side information and the insufficient-sample abort guard retained. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def joinBases {n : Nat} (M : Finset (Fin n))
    (p : (Fin (selectedCount M) → BB84Basis) × (Fin (remainderCount M) → BB84Basis)) :
    Fin n → BB84Basis := fun i =>
  if h : i ∈ M then p.1 ((selectedIndex M).symm ⟨i,h⟩)
  else p.2 ((remainderIndex M).symm ⟨i,h⟩)

def basesEquiv {n : Nat} (M : Finset (Fin n)) : (Fin n → BB84Basis) ≃
    ((Fin (selectedCount M) → BB84Basis) × (Fin (remainderCount M) → BB84Basis)) where
  toFun θ := (bases M θ, remainderBases M θ)
  invFun := joinBases M
  left_inv θ := by
    funext i
    by_cases h : i ∈ M <;> simp [joinBases, bases, remainderBases, h]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp [bases, joinBases]
    · funext i
      simp [remainderBases, joinBases, (remainderIndex M i).property]

/-- Finite joint density matrices preserve the independent uniform split;
the states in the mixture may depend on both choices and be entangled. -/
theorem uniform_bases_split {n : Nat} (M : Finset (Fin n)) {a : Space}
    (ρ : (Fin n → BB84Basis) → Density a) :
    (Density.mixture (Foundation.Probability.uniform (Fin n → BB84Basis)) ρ).matrix =
      (Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis)) (fun θ =>
        Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
          ρ (joinBases M (θ,η))))).matrix := by
  rw [← Density.mixture_uniform_equiv (basesEquiv M).symm, Density.mixture_uniform_product]
  rfl

theorem record_split_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (Randomized.record A k minKey tolerance).matrix =
      (Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
        Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis)) (fun θ =>
          Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
            Density.mixture (BB84SiftingRandomness.testDistribution M k) (fun T =>
              BB84RawSource.state A (joinBases M (θ,η))
                (BB84SiftingRandomness.bobBases (joinBases M (θ,η)) M) T
                (BB84SiftingRandomness.requiredLength M k minKey) tolerance))))).matrix := by
  rw [← BB84SiftingRandomness.record_eq]
  apply Density.mixture_congr_matrix
  intro M
  exact uniform_bases_split M _

end
end Foundation.Quantum.QKD.BB84SiftedInput
