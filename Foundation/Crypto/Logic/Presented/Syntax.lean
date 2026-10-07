import Foundation.Logic.Presentation
import Foundation.Crypto.Logic.General.Derivation

/-! The cryptographic rule language as a finite-arity presentation. Public
parameter types and their pullbacks are opaque data here: this module does not
take a security signature, evaluate a reduction, or assert security. -/
namespace CryptoLogic.Presented

open General
universe a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

structure Parameters {K : CodeSystem} (L : General.Language.{a, b} K) where
  Family : L.Object → Type p
  unary : ∀ {X Y}, General.ReductionExpr L X Y → Family X → Family Y
  left : ∀ {X Y Z}, L.Binary X Y Z → Family X → Family Y
  right : ∀ {X Y Z}, L.Binary X Y Z → Family X → Family Z

structure Claim {K : CodeSystem} {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L) where
  object : L.Object
  family : P.Family object

inductive Rule {K : CodeSystem} {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L) where
  | transport {X Y} (r : General.ReductionExpr L X Y) (F : P.Family X)
  | binary {X Y Z} (e : L.Binary X Y Z) (F : P.Family X)

abbrev presentation {K : CodeSystem} {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L) :
    Foundation.Logic.Presentation where
  Judgment := Claim P
  Rule := Rule P
  arity := fun rule => match rule with
    | .transport _ _ => 1
    | .binary _ _ => 2
  premise := fun rule => match rule with
    | .transport r F => fun _ => ⟨_, P.unary r F⟩
    | .binary e F => Fin.cases ⟨_, P.left e F⟩ (fun _ => ⟨_, P.right e F⟩)
  conclusion := fun rule => match rule with
    | .transport (X := X) _ F => ⟨X, F⟩
    | .binary (X := X) _ F => ⟨X, F⟩

abbrev Context {K : CodeSystem} {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L) :=
  Foundation.Logic.Context (presentation P)

abbrev Derivation {K : CodeSystem} {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L)
    (Γ : Context P) (X : L.Object) (F : P.Family X) :=
  Foundation.Logic.Derivation (presentation P) Γ ⟨X, F⟩

namespace Derivation

variable {K : CodeSystem} {L : General.Language.{a, b} K} {P : Parameters.{a, b, p} L}
  {Γ Δ : Context P}

def transport {X Y} (r : General.ReductionExpr L X Y) (F : P.Family X)
    (child : Derivation P Γ Y (P.unary r F)) : Derivation P Γ X F :=
  Foundation.Logic.Derivation.apply (T := presentation P) (Rule.transport r F) (fun _ => child)

def binary {X Y Z} (e : L.Binary X Y Z) (F : P.Family X)
    (left : Derivation P Γ Y (P.left e F))
    (right : Derivation P Γ Z (P.right e F)) : Derivation P Γ X F :=
  Foundation.Logic.Derivation.apply (T := presentation P) (Rule.binary e F) (Fin.cases left (fun _ => right))

def machines (Γ : Context P) : Fin Γ.length → K.Machine :=
  fun i => L.machine (Γ.claim i).object

/-- Pure code generation uses only the rule names, parameter indices, and
registered compiler syntax. It does not need an interpretation of parameters. -/
def plan {A : Claim P} : Foundation.Logic.Derivation (presentation P) Γ A →
    General.Plan K (machines (P := P) Γ) (L.machine A.object)
  | .hypothesis i => .hypothesis i _ rfl
  | .apply (Rule.transport r _) children => .unary r.compiler (plan (children 0))
  | .apply (Rule.binary e _) children =>
      .binary (L.binaryCompilers e).1 (L.binaryCompilers e).2
        (plan (children 0)) (plan (children 1))

def run {X F} (d : Derivation P Γ X F) (code : K.Code (L.machine X)) :
    List (Nat × Sigma K.Code) :=
  (plan d).run code |>.map (fun (i, packed) => (i.val, packed))

theorem plan_substitute {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A)
    (replacement : ∀ i, Foundation.Logic.Derivation (presentation P) Δ (Γ.claim i)) :
    plan (d.substitute replacement) =
      (plan d).substitute (fun i => plan (replacement i)) := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => plan (d.substitute replacement) =
      (plan d).substitute (fun i => plan (replacement i)))
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F => exact congrArg (General.Plan.unary r.compiler) (ih 0)
  | binary e F =>
      exact congrArg₂
        (General.Plan.binary (L.binaryCompilers e).1 (L.binaryCompilers e).2) (ih 0) (ih 1)

end Derivation

/-- A genuinely symbolic choice of parameter language. Pullback expressions
are constructors; interpretation is supplied in a different module. -/
inductive FamilyExpr {K : CodeSystem} {L : General.Language.{a, b} K}
    (Seed : L.Object → Type p) : L.Object → Type (max a b p) where
  | atom {X} : Seed X → FamilyExpr Seed X
  | unary {X Y} : General.ReductionExpr L X Y → FamilyExpr Seed X → FamilyExpr Seed Y
  | left {X Y Z} : L.Binary X Y Z → FamilyExpr Seed X → FamilyExpr Seed Y
  | right {X Y Z} : L.Binary X Y Z → FamilyExpr Seed X → FamilyExpr Seed Z

def symbolicParameters {K : CodeSystem} {L : General.Language.{a, b} K}
    (Seed : L.Object → Type p) : Parameters L where
  Family := FamilyExpr Seed
  unary := FamilyExpr.unary
  left := FamilyExpr.left
  right := FamilyExpr.right

end CryptoLogic.Presented
