import Foundation.Relation.ReducesTo

universe u v w

/-- Each goal reduces to the other. -/
def Equivalent (P : CryptoGoal.{u}) (Q : CryptoGoal.{v}) : Prop :=
  ReducesTo P Q ∧ ReducesTo Q P

namespace Equivalent

theorem refl (P : CryptoGoal.{u}) : Equivalent P P :=
  ⟨ReducesTo.refl P, ReducesTo.refl P⟩

theorem symm {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (h : Equivalent P Q) : Equivalent Q P :=
  ⟨h.2, h.1⟩

theorem trans {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {R : CryptoGoal.{w}}
    (hPQ : Equivalent P Q) (hQR : Equivalent Q R) : Equivalent P R :=
  ⟨ReducesTo.trans hPQ.1 hQR.1, ReducesTo.trans hQR.2 hPQ.2⟩

end Equivalent
