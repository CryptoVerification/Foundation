import Foundation.Crypto.Logic.Presented.Translation

/-! A two-stage reduction offered as a single derived inference rule. The
source theory retains all old rules and adds the macro. Expansion preserves
emitted code and advantage bounds; resource certificates use the expanded
explicit tree and are kept in their backend's original units. -/
namespace CryptoLogic.Presented.CompositeRule

open scoped ENNReal
universe u v a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {K : General.CodeSystem} {L : General.Language.{a, b} K}

inductive Rule (P : Parameters.{a, b, p} L) where
  | base : Presented.Rule P → Rule P
  | seq {X Y Z} (first : General.ReductionExpr L X Y)
      (second : General.ReductionExpr L Y Z) (F : P.Family X) : Rule P

abbrev presentation (P : Parameters L) : Foundation.Logic.Presentation where
  Judgment := Claim P
  Rule := Rule P
  arity := fun | .base r => (Presented.presentation P).arity r | .seq _ _ _ => 1
  premise := fun
    | .base r => (Presented.presentation P).premise r
    | .seq r s F => fun _ => ⟨_, P.unary s (P.unary r F)⟩
  conclusion := fun
    | .base r => (Presented.presentation P).conclusion r
    | .seq (X := X) _ _ F => ⟨X, F⟩

variable {P : Parameters.{a, b, p} L}

/-- A macro is justified by an actual proof, rather than by adding a new
security axiom or postulating that arbitrary compilers preserve security. -/
abbrev expansion : Foundation.Logic.Translation (presentation P) (Presented.presentation P) where
  judgment := id
  rule := fun rule => match rule with
    | .base r => Foundation.Logic.Derivation.apply (T := Presented.presentation P) r
        (fun i => Foundation.Logic.Derivation.hypothesis (T := Presented.presentation P)
          (Γ := ((presentation P).ruleContext (.base r)).map id) i)
    | .seq r s F => Presented.Derivation.transport r F
        (Presented.Derivation.transport s (P.unary r F)
          (Foundation.Logic.Derivation.hypothesis (T := Presented.presentation P)
            (Γ := ((presentation P).ruleContext (.seq r s F)).map id) 0))

/-- The compact code interpretation executes the composed compiler in one
operation; the expansion executes the two compiler stages. -/
def compactCode (P : Parameters L) (length : Nat) : Foundation.Logic.Model (presentation P) where
  Carrier := fun A => K.Code (L.machine A.object) → List (General.Plan.Output K length)
  operation := fun rule children code => match rule with
    | .base (.transport r _) => children 0 (r.compiler.run code)
    | .base (.binary e _) => children 0 ((L.binaryCompilers e).1.run code) ++
        children 1 ((L.binaryCompilers e).2.run code)
    | .seq r s _ => children 0 ((r.compiler.comp s.compiler).run code)

theorem compactCode_pullback (length : Nat) : compactCode P length =
    (expansion (P := P)).pullback (Presented.codeModel P length) := by
  unfold compactCode Foundation.Logic.Translation.pullback
  congr 1
  funext rule children code
  cases rule with
  | base r => cases r <;> rfl
  | seq r s F => rfl

def codePreservation (length : Nat) : Foundation.Logic.Model.Hom (compactCode P length)
    ((expansion (P := P)).pullback (Presented.codeModel P length)) where
  map := fun _ value => value
  preserves := by
    intro rule children
    cases rule with
    | base r => cases r <;> rfl
    | seq r s F => rfl

/-- Exact emitted codes, for arbitrary macro proofs and arbitrary source code. -/
theorem code_preserved {Γ : Foundation.Logic.Context (presentation P)} {A}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    d.eval (compactCode P Γ.length)
      (fun i code => [(i, ⟨L.machine (Γ.claim i).object, code⟩)]) =
    (Presented.Derivation.plan ((expansion (P := P)).translate d)).run := by
  calc
    _ = ((expansion (P := P)).translate d).eval (Presented.codeModel P Γ.length)
        (fun i code => [(i, ⟨L.machine (Γ.claim i).object, code⟩)]) :=
      (Foundation.Logic.Translation.eval_preserving _ (codePreservation Γ.length) _ d).symm
    _ = _ := Presented.code_eval _

/-- Direct advantage analysis contracts the two losses into their composed
monotone bound, rather than retaining two unary loss-tree nodes. -/
def compactLoss (S : General.Signature.{u, v} L) (length : Nat) :
    Foundation.Logic.Model (presentation P) where
  Carrier := fun _ => (Fin length → Nat → ℝ≥0∞) → Nat → ℝ≥0∞
  operation := fun rule children ε n => match rule with
    | .base (.transport r _) => (r.eval S).reduction.loss.eval n (children 0 ε n)
    | .base (.binary e _) => (S.binary e).leftLoss.eval n (children 0 ε n) +
        (S.binary e).rightLoss.eval n (children 1 ε n)
    | .seq r s _ => ((r.eval S).reduction.loss.comp (s.eval S).reduction.loss).eval n (children 0 ε n)

theorem compactLoss_pullback (S : General.Signature.{u, v} L) (length : Nat) :
    compactLoss (P := P) S length =
      (expansion (P := P)).pullback (Presented.advantageModel P S length) := by
  unfold compactLoss Foundation.Logic.Translation.pullback
  congr 1
  funext rule children ε n
  cases rule with
  | base r => cases r <;> rfl
  | seq r s F => rfl

def lossPreservation (S : General.Signature.{u, v} L) (length : Nat) :
    Foundation.Logic.Model.Hom (compactLoss (P := P) S length)
      ((expansion (P := P)).pullback (Presented.advantageModel P S length)) where
  map := fun _ value => value
  preserves := by
    intro rule children
    cases rule with
    | base r => cases r <;> rfl
    | seq r s F => rfl

/-- Exact numerical advantage bound, for all source proofs and every profile
of premise advantages, not just for negligible profiles. -/
theorem loss_preserved {S : General.Signature.{u, v} L} (M : Interpretation P S)
    {Γ : Foundation.Logic.Context (presentation P)} {A}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    d.eval (compactLoss (P := P) S Γ.length) (fun i ε n => ε i n) =
      fun ε n => (M.loss ((expansion (P := P)).translate d)).eval ε n := by
  calc
    _ = ((expansion (P := P)).translate d).eval (Presented.advantageModel P S Γ.length)
        (fun i ε n => ε i n) :=
      (Foundation.Logic.Translation.eval_preserving _ (lossPreservation S Γ.length) _ d).symm
    _ = _ := Presented.advantage_eval M _

/-- Concrete security using the compact, independently specified analysis. -/
theorem bounded {S : General.Signature.{u, v} L} (M : Interpretation P S)
    {Γ : Foundation.Logic.Context (presentation P)} {X F}
    (d : Foundation.Logic.Derivation (presentation P) Γ ⟨X, F⟩) (ε)
    (hε : ∀ i, (S.interpret (Γ.claim i).object).Bounded (M.family (Γ.claim i).family) (ε i)) :
    (S.interpret X).Bounded (M.family F)
      (d.eval (compactLoss (P := P) S Γ.length) (fun i ε n => ε i n) ε) := by
  rw [loss_preserved M]
  exact M.bounded ((expansion (P := P)).translate d) ε hε

/-- Resources are specified by the target proof-tree interpretation, rather
than assigning fictitious universal time or query units to the source rules. -/
def resourceModel {S : General.Signature.{u, v} L} (M : Interpretation P S)
    (Γ : Foundation.Logic.Context (presentation P)) : Foundation.Logic.Model (presentation P) :=
  (expansion (P := P)).pullback (M.treeModel (Γ.map id))

theorem tree_preserved {S : General.Signature.{u, v} L} (M : Interpretation P S)
    {Γ : Foundation.Logic.Context (presentation P)} {A}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    d.eval (resourceModel M Γ)
      (fun i => General.Tree.hypothesis (S := S) (Γ := M.context (Γ.map id)) i) =
      M.tree ((expansion (P := P)).translate d) :=
  (Foundation.Logic.Translation.eval_translate (expansion (P := P)) _ _ d).symm

end CryptoLogic.Presented.CompositeRule
