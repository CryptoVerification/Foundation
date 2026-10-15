import Foundation.Crypto.Logic.Polygraph.Syntax
import Foundation.Crypto.Logic.Presented.Resources

/-! Security is transported through the selected reconstructed tree. No
security axiom or new interpretation of an arbitrary compiler is introduced. -/
namespace CryptoLogic.Polygraph

open General
universe u v a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace Derivation

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}
  {S : General.Signature.{u, v} L}

def tree (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F) :=
  M.tree (toPresented d)

def loss (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F) :=
  M.loss (toPresented d)

theorem sound (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F)
    (h : ∀ i, (S.interpret (Γ.claim i).object).Secure (M.family (Γ.claim i).family)) :
    (S.interpret X).Secure (M.family F) :=
  M.sound (toPresented d) h

theorem bounded (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F)
    (ε) (h : ∀ i, (S.interpret (Γ.claim i).object).Bounded
      (M.family (Γ.claim i).family) (ε i)) :
    (S.interpret X).Bounded (M.family F) (fun n => (loss M d).eval ε n) :=
  M.bounded (toPresented d) ε h

@[simp] theorem tree_ofPresented (M : Presented.Interpretation P S) {X F}
    (d : Presented.Derivation P Γ X F) : tree M (ofPresented d) = M.tree d := by
  simp [tree]

@[simp] theorem loss_ofPresented (M : Presented.Interpretation P S) {X F}
    (d : Presented.Derivation P Γ X F) : loss M (ofPresented d) = M.loss d := by
  simp [loss]

theorem loss_substitute (M : Presented.Interpretation P S)
    {Δ : Presented.Context P} {X F} (d : Derivation P Γ X F)
    (replacement : ∀ i, Derivation P Δ (Γ.claim i).object (Γ.claim i).family) :
    loss M (substitute d replacement) =
      (loss M d).substitute (fun i => loss M (replacement i)) := by
  simp only [loss, toPresented_substitute]
  exact M.loss_substitute _ _

end Derivation
end CryptoLogic.Polygraph
