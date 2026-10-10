import Foundation.Quantum.QKD.SubnormalizedRelabel

namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem restrict_intersection {X : Type} [Fintype X] {e : Space} (ρ : State X e)
    (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] :
    restrict (restrict ρ P) Q = restrict ρ (fun x => P x ∧ Q x) := by
  apply State.ext
  funext x
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [restrict,hp,hq]

end
end Foundation.Quantum.QKD.Subnormalized
