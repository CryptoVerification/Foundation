import Foundation.Crypto.Logic.Presented.Syntax
import Foundation.Crypto.Meta.General.Metatheory

/-! Security is an interpretation of the pure presentation. The public-family
interpretation must commute with every parameter pullback. Code generation
does not receive this interpretation. -/
namespace CryptoLogic.Presented

open General
universe u v a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

structure Interpretation {K : CodeSystem} {L : General.Language.{a, b} K}
    (P : Parameters.{a, b, p} L) (S : General.Signature.{u, v} L) where
  family : ∀ {X}, P.Family X → InstanceFamily (S.interpret X).goal
  unary : ∀ {X Y} (r : General.ReductionExpr L X Y) F,
    family (P.unary r F) = (r.eval S).reduction.mapFamily (family F)
  left : ∀ {X Y Z} (e : L.Binary X Y Z) F,
    family (P.left e F) = (S.binary e).left.transform.mapFamily (family F)
  right : ∀ {X Y Z} (e : L.Binary X Y Z) F,
    family (P.right e F) = (S.binary e).right.transform.mapFamily (family F)

namespace Interpretation

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Parameters.{a, b, p} L} {S : General.Signature.{u, v} L}

def context (M : Interpretation P S) (Γ : Presented.Context P) : General.Context S where
  length := Γ.length
  claim i := ⟨(Γ.claim i).object, M.family (Γ.claim i).family⟩

/-- The proof-relevant security model keeps the actual registered trees,
including their selected loss and execution certificates. -/
def treeModel (M : Interpretation P S) (Γ : Presented.Context P) :
    Foundation.Logic.Model (presentation P) where
  Carrier := fun A => General.Tree S (M.context Γ) A.object (M.family A.family)
  operation := fun rule children => match rule with
    | .transport r F => General.Tree.transport r (M.family F) (M.unary r F ▸ children 0)
    | .binary e F => General.Tree.binary e (M.family F)
        (M.left e F ▸ children 0) (M.right e F ▸ children 1)

def tree (M : Interpretation P S) {Γ : Presented.Context P} {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    General.Tree S (M.context Γ) A.object (M.family A.family) :=
  d.eval (M.treeModel Γ) (fun i => General.Tree.hypothesis (S := S) (Γ := M.context Γ) i)

/-- Family equality transports commute with replacing hypothesis trees. -/
private theorem substitute_cast {Γ Δ : General.Context S} {X}
    {F G : InstanceFamily (S.interpret X).goal} (h : F = G)
    (t : General.Tree S Γ X F)
    (replacement : ∀ i, General.Tree S Δ (Γ.claim i).object (Γ.claim i).family) :
    (h ▸ t : General.Tree S Γ X G).substitute replacement =
      h ▸ t.substitute replacement := by cases h; rfl

/-- Interpreting cut keeps the entire proof tree, including loss and witnesses. -/
theorem tree_substitute (M : Interpretation P S) {Γ Δ : Presented.Context P}
    {A : Claim P} (d : Foundation.Logic.Derivation (presentation P) Γ A)
    (replacement : ∀ i, Foundation.Logic.Derivation (presentation P) Δ (Γ.claim i)) :
    M.tree (d.substitute replacement) =
      (M.tree d).substitute (fun i => M.tree (replacement i)) := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => M.tree (d.substitute replacement) =
      (M.tree d).substitute (fun i => M.tree (replacement i)))
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F =>
      change General.Tree.transport r (M.family F)
        (M.unary r F ▸ M.tree ((children 0).substitute replacement)) =
        General.Tree.transport r (M.family F)
          ((M.unary r F ▸ M.tree (children 0)).substitute _)
      rw [substitute_cast, ih 0]
  | binary e F =>
      change General.Tree.binary e (M.family F)
        (M.left e F ▸ M.tree ((children 0).substitute replacement))
        (M.right e F ▸ M.tree ((children 1).substitute replacement)) =
        General.Tree.binary e (M.family F)
          ((M.left e F ▸ M.tree (children 0)).substitute _)
          ((M.right e F ▸ M.tree (children 1)).substitute _)
      rw [substitute_cast, substitute_cast, ih 0, ih 1]

/-- Truth-valued semantics is a separate model of the same presentation. -/
def securityModel (M : Interpretation P S) : Foundation.Logic.Model (presentation P) where
  Carrier := fun A => (S.interpret A.object).Secure (M.family A.family)
  operation := fun rule children => match rule with
    | .transport r F => (r.eval S).secure (M.family F) (M.unary r F ▸ children 0)
    | .binary e F => (S.binary e).secure (M.family F)
        (M.left e F ▸ children 0) (M.right e F ▸ children 1)

theorem sound (M : Interpretation P S) {Γ : Presented.Context P} {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A)
    (hypotheses : ∀ i, (S.interpret (Γ.claim i).object).Secure (M.family (Γ.claim i).family)) :
    (S.interpret A.object).Secure (M.family A.family) := d.eval M.securityModel hypotheses

/-- Reindexing a semantic family changes no compiler plan. -/
private theorem plan_cast {Γ : General.Context S} {X} {F G : InstanceFamily (S.interpret X).goal}
    (h : F = G) (tree : General.Tree S Γ X F) :
    (h ▸ tree : General.Tree S Γ X G).plan = tree.plan := by cases h; rfl

theorem tree_plan (M : Interpretation P S) {Γ : Presented.Context P} {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    (M.tree d).plan = Presented.Derivation.plan d := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => (M.tree d).plan = Presented.Derivation.plan d)
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F =>
      change General.Plan.unary r.compiler (M.unary r F ▸ M.tree (children 0)).plan = _
      rw [plan_cast, ih 0]
      rfl
  | binary e F =>
      change General.Plan.binary (L.binaryCompilers e).1 (L.binaryCompilers e).2
        (M.left e F ▸ M.tree (children 0)).plan (M.right e F ▸ M.tree (children 1)).plan = _
      rw [plan_cast, plan_cast, ih 0, ih 1]
      rfl

/-- Runtime fields come directly from syntax. Only the erased typing
certificate interprets the semantic tree. -/
@[macro_inline] def legacy (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) :
    General.Derivation S (M.context Γ) X (M.family F) where
  plan := Presented.Derivation.plan d
  compilers := (Presented.Derivation.plan d).paths
  emitted_eq := General.Plan.paths_run _
  typed := ⟨M.tree d, M.tree_plan d⟩

theorem legacy_run (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (code : K.Code (L.machine X)) :
    (M.legacy d).run code = Presented.Derivation.run d code := by
  rw [General.Derivation.run_eq]
  rfl

end Interpretation

namespace FamilyExpr

variable {K : CodeSystem} {L : General.Language.{a, b} K} {Seed : L.Object → Type p}

def eval (S : General.Signature.{u, v} L)
    (atoms : ∀ X, Seed X → InstanceFamily (S.interpret X).goal) :
    {X : L.Object} → FamilyExpr Seed X → InstanceFamily (S.interpret X).goal
  | X, .atom seed => atoms X seed
  | _, .unary r F => (r.eval S).reduction.mapFamily (eval S atoms F)
  | _, .left e F => (S.binary e).left.transform.mapFamily (eval S atoms F)
  | _, .right e F => (S.binary e).right.transform.mapFamily (eval S atoms F)

def interpretation (S : General.Signature.{u, v} L)
    (atoms : ∀ X, Seed X → InstanceFamily (S.interpret X).goal) :
    Interpretation (symbolicParameters Seed) S where
  family := eval S atoms
  unary := by intros; rfl
  left := by intros; rfl
  right := by intros; rfl

end FamilyExpr
end CryptoLogic.Presented
