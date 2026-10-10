import Foundation.Quantum.QKD.SubnormalizedZero

/-! Zero accepted mass contributes zero to the secrecy error, while the full
abort state is kept outside the accepted part. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Subnormalized

theorem mixture_zero {S X : Type} [Fintype S] [Fintype X] {e : Space} (p : PMF S) :
    mixture p (fun _ => (zero : State X e)) = zero := by
  apply State.ext
  funext x
  simp [mixture, zero]

end Subnormalized
namespace CommonKey
open Subnormalized

theorem uniformize_zero {K T : Type} [Fintype K] [Nonempty K] [Fintype T] {e : Space} :
    uniformize (zero : State (K × T) e) = zero := by
  apply State.ext
  funext x
  simp [uniformize, zero]

theorem zero_secrecy {K T : Type} [Fintype K] [Nonempty K] [Fintype T] {e : Space} :
    OperatorApprox (joint (zero : State (K × T) e)) (joint (uniformize (zero : State (K × T) e))) 0 := by
  rw [uniformize_zero]
  exact OperatorApprox.refl _

end CommonKey
end
end Foundation.Quantum.QKD
