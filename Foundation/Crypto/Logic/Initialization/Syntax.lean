import Foundation.Logic.Presentation

/-! A pure initialization rule. Syntax contains neither machines nor
probability distributions; its interpretation supplies executable contracts. -/
namespace CryptoLogic.Initialization
open Foundation.Logic

inductive Budget where
  | leftInit | rightInit | leftSuffix | rightSuffix
  | add : Budget → Budget → Budget
  deriving DecidableEq, Repr

inductive Claim where
  | generated
  | continuation
  | experiment (left right : Budget)
  deriving DecidableEq, Repr

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Unit
  arity := fun _ => 2
  premise := fun _ => Fin.cases .generated (fun _ => .continuation)
  conclusion := fun _ => .experiment (.add .leftInit .leftSuffix) (.add .rightInit .rightSuffix)

abbrev context : Context presentation where
  length := 2
  claim := Fin.cases .generated (fun _ => .continuation)

/-- One proof is reused for every machine, key type and observation type. -/
def proof : Derivation presentation context
    (.experiment (.add .leftInit .leftSuffix) (.add .rightInit .rightSuffix)) :=
  Derivation.apply (T := presentation) ()
    (fun i => Derivation.hypothesis (T := presentation) (Γ := context) i)

def Budget.eval (leftInit rightInit leftSuffix rightSuffix : Nat) : Budget → Nat
  | .leftInit => leftInit
  | .rightInit => rightInit
  | .leftSuffix => leftSuffix
  | .rightSuffix => rightSuffix
  | .add first second => first.eval leftInit rightInit leftSuffix rightSuffix +
      second.eval leftInit rightInit leftSuffix rightSuffix

end CryptoLogic.Initialization
