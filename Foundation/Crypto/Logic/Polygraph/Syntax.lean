import Foundation.Logic.Polygraph.Interpretation
import Foundation.Crypto.Logic.Presented.Syntax

/-! Pure logical diagrams over the existing cryptographic rule presentation.
Code extraction does not require a security signature or interpretation. -/
namespace CryptoLogic.Polygraph

open General
universe a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

abbrev Derivation {K : CodeSystem} {L : General.Language.{a, b} K}
    (P : Presented.Parameters.{a, b, p} L) (Γ : Presented.Context P)
    (X : L.Object) (F : P.Family X) :=
  Foundation.Logic.Polygraph.Diagram (Presented.presentation P) Γ
    (Foundation.Logic.Context.singleton ⟨X, F⟩)

namespace Derivation

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}

def toPresented {X F} (d : Derivation P Γ X F) : Presented.Derivation P Γ X F :=
  d.toDerivation

def ofPresented {X F} (d : Presented.Derivation P Γ X F) : Derivation P Γ X F :=
  Foundation.Logic.Polygraph.Diagram.ofDerivation d

@[simp] theorem toPresented_ofPresented {X F} (d : Presented.Derivation P Γ X F) :
    toPresented (ofPresented d) = d :=
  Foundation.Logic.Polygraph.Diagram.toDerivation_ofDerivation d

def hypothesis (i : Fin Γ.length) : Derivation P Γ (Γ.claim i).object (Γ.claim i).family :=
  .wiring (Foundation.Logic.Polygraph.Wiring.select Γ i)

def transport {X Y} (r : General.ReductionExpr L X Y) (F : P.Family X)
    (child : Derivation P Γ Y (P.unary r F)) : Derivation P Γ X F :=
  .seq child (.generator (T := Presented.presentation P) (Presented.Rule.transport r F))

def binary {X Y Z} (e : L.Binary X Y Z) (F : P.Family X)
    (left : Derivation P Γ Y (P.left e F)) (right : Derivation P Γ Z (P.right e F)) :
    Derivation P Γ X F :=
  .seq (.tuple (Δ := (Presented.presentation P).ruleContext (Presented.Rule.binary e F))
    (Fin.cases left (fun _ => right)))
    (.generator (T := Presented.presentation P) (Presented.Rule.binary e F))

def plan {X F} (d : Derivation P Γ X F) := Presented.Derivation.plan (toPresented d)

def run {X F} (d : Derivation P Γ X F) (code : K.Code (L.machine X)) :=
  Presented.Derivation.run (toPresented d) code

def substitute {Δ : Presented.Context P} {X F} (d : Derivation P Γ X F)
    (replacement : ∀ i, Derivation P Δ (Γ.claim i).object (Γ.claim i).family) :
    Derivation P Δ X F :=
  Foundation.Logic.Polygraph.Diagram.substitute d (fun i => toPresented (replacement i))

@[simp] theorem toPresented_substitute {Δ : Presented.Context P} {X F}
    (d : Derivation P Γ X F)
    (replacement : ∀ i, Derivation P Δ (Γ.claim i).object (Γ.claim i).family) :
    toPresented (substitute d replacement) =
      (toPresented d).substitute (fun i => toPresented (replacement i)) :=
  Foundation.Logic.Polygraph.Diagram.toForest_substitute d _ 0

theorem plan_substitute {Δ : Presented.Context P} {X F}
    (d : Derivation P Γ X F)
    (replacement : ∀ i, Derivation P Δ (Γ.claim i).object (Γ.claim i).family) :
    plan (substitute d replacement) = (plan d).substitute (fun i => plan (replacement i)) := by
  simp only [plan, toPresented_substitute]
  exact Presented.Derivation.plan_substitute _ _

@[simp] theorem run_ofPresented {X F} (d : Presented.Derivation P Γ X F)
    (code : K.Code (L.machine X)) :
    run (ofPresented d) code = Presented.Derivation.run d code := by
  simp [run]

end Derivation
end CryptoLogic.Polygraph
