import Foundation.Logic.Polygraph.DiagramNormalization
import Foundation.Crypto.Logic.Polygraph.Resources

/-! Every structural three-path preserves the selected tree, exact emitted
code, loss expression, and entire backend-specific execution certificate.
This is stronger than comparing final safety propositions or output laws. -/
namespace CryptoLogic.Polygraph.Derivation

open General
universe u v a b p
set_option linter.checkUnivs false
variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}
  {S : General.Signature.{u, v} L} {X F}
  {d e : Derivation P Γ X F}

abbrev StructuralPath (d e : Derivation P Γ X F) :=
  Foundation.Logic.Polygraph.Diagram.Cell3 d e

theorem presented_eq (path : StructuralPath d e) : toPresented d = toPresented e :=
  congrFun path.forest_eq 0

theorem run_path (path : StructuralPath d e) (code : K.Code (L.machine X)) :
    run d code = run e code := by simp only [run, presented_eq path]

theorem tree_path (path : StructuralPath d e) (M : Presented.Interpretation P S) :
    tree M d = tree M e := by simp only [tree, presented_eq path]

theorem loss_path (path : StructuralPath d e) (M : Presented.Interpretation P S) :
    loss M d = loss M e := by simp only [loss, presented_eq path]

theorem witnesses_path (path : StructuralPath d e) (M : Presented.Interpretation P S)
    (A) (W : (S.interpret X).Witness (M.family F) A) :
    runWitnesses M d A W = runWitnesses M e A W := by
  simp only [runWitnesses, presented_eq path]

def normalize (d : Derivation P Γ X F) : Derivation P Γ X F :=
  Foundation.Logic.Polygraph.Diagram.normalize d

def normalizePath (d : Derivation P Γ X F) : StructuralPath d (normalize d) :=
  Foundation.Logic.Polygraph.Diagram.normalizePath d

@[simp] theorem normalize_run (d : Derivation P Γ X F) (code : K.Code (L.machine X)) :
    run (normalize d) code = run d code := (run_path (normalizePath d) code).symm

@[simp] theorem normalize_loss (d : Derivation P Γ X F) (M : Presented.Interpretation P S) :
    loss M (normalize d) = loss M d := (loss_path (normalizePath d) M).symm

@[simp] theorem normalize_witnesses (d : Derivation P Γ X F)
    (M : Presented.Interpretation P S) (A) (W : (S.interpret X).Witness (M.family F) A) :
    runWitnesses M (normalize d) A W = runWitnesses M d A W :=
  (witnesses_path (normalizePath d) M A W).symm

end CryptoLogic.Polygraph.Derivation
