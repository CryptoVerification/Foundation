import Foundation.Core.Reduction

universe u v w

/-- There exists a quantitative reduction from `P` to `Q`. -/
def ReducesTo (P : CryptoGoal.{u}) (Q : CryptoGoal.{v}) : Prop :=
  Nonempty (Reduction P Q)

namespace ReducesTo

theorem refl (P : CryptoGoal.{u}) : ReducesTo P P :=
  ⟨Reduction.id P⟩

theorem trans {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {R : CryptoGoal.{w}}
    (hPQ : ReducesTo P Q) (hQR : ReducesTo Q R) : ReducesTo P R := by
  obtain ⟨r₁⟩ := hPQ
  obtain ⟨r₂⟩ := hQR
  exact ⟨r₁.comp r₂⟩

end ReducesTo
