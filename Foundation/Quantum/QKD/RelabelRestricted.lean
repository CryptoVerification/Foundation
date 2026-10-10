import Foundation.Quantum.QKD.SeededSubnormalized

namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem relabel_restrict_congr {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] {e : Space}
    (ρ : State X e) (P : X → Prop) [DecidablePred P] (f g : X → Y)
    (hfg : ∀ x, P x → f x = g x) : relabel (restrict ρ P) f = relabel (restrict ρ P) g := by
  apply State.ext
  funext y
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x
  · simp only [restrict, hx, ite_true, hfg x hx]
  · simp only [restrict, hx, ite_false]
    split_ifs <;> rfl

theorem ofCQ_relabel {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] {e : Space}
    (ρ : Guessing.CQ X e) (f : X → Y) : ofCQ (Guessing.relabel ρ f) = relabel (ofCQ ρ) f := rfl

end
end Foundation.Quantum.QKD.Subnormalized
