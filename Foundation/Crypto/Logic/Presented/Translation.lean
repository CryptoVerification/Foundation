import Foundation.Logic.Translation
import Foundation.Crypto.Logic.Presented.Resources

/-! Code is an interpretation of the rule presentation, independently of
security semantics. A derived-rule translation can consequently certify its
code behavior by the general interpretation theorem. -/
namespace CryptoLogic.Presented

universe u v a b p
open scoped ENNReal
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {K : General.CodeSystem} {L : General.Language.{a, b} K}
  {P : Parameters.{a, b, p} L}

def codeModel (P : Parameters L) (length : Nat) : Foundation.Logic.Model (presentation P) where
  Carrier := fun A => K.Code (L.machine A.object) → List (General.Plan.Output K length)
  operation := fun rule children code => match rule with
    | .transport r _ => children 0 (r.compiler.run code)
    | .binary e _ => children 0 ((L.binaryCompilers e).1.run code) ++
        children 1 ((L.binaryCompilers e).2.run code)

theorem code_eval {Γ : Presented.Context P} {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    d.eval (codeModel P Γ.length)
      (fun i code => [(i, ⟨L.machine (Γ.claim i).object, code⟩)]) =
      (Presented.Derivation.plan d).run := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => d.eval (codeModel P Γ.length)
      (fun i code => [(i, ⟨L.machine (Γ.claim i).object, code⟩)]) =
        (Presented.Derivation.plan d).run)
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F =>
      funext code
      exact congrFun (ih 0) (r.compiler.run code)
  | binary e F =>
      funext code
      exact congrArg₂ (· ++ ·)
        (congrFun (ih 0) ((L.binaryCompilers e).1.run code))
        (congrFun (ih 1) ((L.binaryCompilers e).2.run code))

/-- Numeric loss interpretation supplied by the registered semantic rules.
This model makes no security assertion until a family interpretation is given. -/
def advantageModel (P : Parameters L) (S : General.Signature.{u, v} L) (length : Nat) :
    Foundation.Logic.Model (presentation P) where
  Carrier := fun _ => (Fin length → Nat → ℝ≥0∞) → Nat → ℝ≥0∞
  operation := fun rule children ε n => match rule with
    | .transport r _ => (r.eval S).reduction.loss.eval n (children 0 ε n)
    | .binary e _ => (S.binary e).leftLoss.eval n (children 0 ε n) +
        (S.binary e).rightLoss.eval n (children 1 ε n)

private theorem loss_cast {S : General.Signature.{u, v} L} {Γ : General.Context S} {X}
    {F G : InstanceFamily (S.interpret X).goal} (h : F = G) (t : General.Tree S Γ X F) :
    (h ▸ t : General.Tree S Γ X G).loss = t.loss := by cases h; rfl

theorem advantage_eval {S : General.Signature.{u, v} L} (M : Interpretation P S)
    {Γ : Presented.Context P} {A : Claim P}
    (d : Foundation.Logic.Derivation (presentation P) Γ A) :
    d.eval (advantageModel P S Γ.length) (fun i ε n => ε i n) =
      fun ε n => (M.loss d).eval ε n := by
  refine Foundation.Logic.Derivation.rec
    (motive := fun A d => d.eval (advantageModel P S Γ.length) (fun i ε n => ε i n) =
      fun ε n => (M.loss d).eval ε n)
    (fun _ => rfl) (fun rule children ih => ?_) d
  cases rule with
  | transport r F =>
      funext ε n
      change (r.eval S).reduction.loss.eval n
        ((children 0).eval (advantageModel P S Γ.length) (fun i ε n => ε i n) ε n) =
        (r.eval S).reduction.loss.eval n ((M.unary r F ▸ M.tree (children 0)).loss.eval ε n)
      rw [loss_cast]
      exact congrArg ((r.eval S).reduction.loss.eval n) (congrFun (congrFun (ih 0) ε) n)
  | binary e F =>
      funext ε n
      change (S.binary e).leftLoss.eval n
        ((children 0).eval (advantageModel P S Γ.length) (fun i ε n => ε i n) ε n) +
        (S.binary e).rightLoss.eval n
          ((children 1).eval (advantageModel P S Γ.length) (fun i ε n => ε i n) ε n) =
        (S.binary e).leftLoss.eval n ((M.left e F ▸ M.tree (children 0)).loss.eval ε n) +
        (S.binary e).rightLoss.eval n ((M.right e F ▸ M.tree (children 1)).loss.eval ε n)
      rw [loss_cast, loss_cast]
      exact congrArg₂ (· + ·)
        (congrArg ((S.binary e).leftLoss.eval n) (congrFun (congrFun (ih 0) ε) n))
        (congrArg ((S.binary e).rightLoss.eval n) (congrFun (congrFun (ih 1) ε) n))

end CryptoLogic.Presented
