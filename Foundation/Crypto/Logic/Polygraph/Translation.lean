import Foundation.Crypto.Logic.Polygraph.Interpretation
import Foundation.Crypto.Logic.Presented.Translation

/-! The independent code and numeric models evaluate diagrams directly.
Reconstruction is proved to commute with these evaluations. -/
namespace CryptoLogic.Polygraph.Derivation

open General
universe u v a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}

theorem code_eval {X F} (d : Derivation P Γ X F) :
    d.eval (Presented.codeModel P Γ.length)
      (fun i code => [(i, ⟨L.machine (Γ.claim i).object, code⟩)]) 0 = (plan d).run := by
  rw [← Foundation.Logic.Polygraph.Diagram.eval_toForest]
  exact Presented.code_eval (toPresented d)

theorem advantage_eval {S : General.Signature.{u, v} L}
    (M : Presented.Interpretation P S) {X F} (d : Derivation P Γ X F) :
    d.eval (Presented.advantageModel P S Γ.length) (fun i ε n => ε i n) 0 =
      fun ε n => (loss M d).eval ε n := by
  rw [← Foundation.Logic.Polygraph.Diagram.eval_toForest]
  exact Presented.advantage_eval M (toPresented d)

end CryptoLogic.Polygraph.Derivation
