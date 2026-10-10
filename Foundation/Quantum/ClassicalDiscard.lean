import Foundation.Quantum.ClassicalMap
import Foundation.Quantum.DiscardMiddle

/-! Public relabelling and discarding a private quantum subsystem commute
as operations on arbitrary joint operators, including correlated states. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem classicalMap_discardMiddle {n m : Nat} (b c : Space) (f : Fin n → Fin m)
    (ρ : Operator (.tensor (.register n) (.tensor b c))) :
    (discardMiddle (.register m) b c).toKraus.apply
      ((classicalMap (.tensor b c) f).toKraus.apply ρ) =
    (classicalMap c f).toKraus.apply
      ((discardMiddle (.register n) b c).toKraus.apply ρ) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [discardMiddle_apply, classicalMap_apply]
  have hc (u : b.Basis) := classicalMap_apply (.tensor b c) f ρ r s (u,i) (u,j)
  have hd (t : Fin n) := discardMiddle_apply (.register n) b c ρ t t i j
  simp_rw [hc, hd]
  by_cases h : r = s
  · subst s
    simp only [ite_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : f t = r <;> simp [ht]
  · simp [h]

end
end Foundation.Quantum
