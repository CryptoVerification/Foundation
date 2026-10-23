import Foundation.Logic.SharedInferenceCompilation

/-! Export closed ordinary inference derivations to the same rule-tree
interface used by diagram compilation. This exporter does not inspect Cells,
normalization strategies, semantic models, or cryptographic programs. -/
namespace Foundation.Logic.SharedInference
universe j r
variable {T : Presentation.{j, r}}

def closedTree : {claim : T.Judgment} → Derivation T (Context.empty T) claim → Tree T.Rule
  | _, .hypothesis index => Fin.elim0 index
  | _, .apply rule children => .node rule (List.ofFn (fun index => closedTree (children index)))

def treeModel (T : Presentation.{j, r}) : Model T where
  Carrier _ := Tree T.Rule
  operation rule children := .node rule (List.ofFn children)

theorem closedTree_eval {claim : T.Judgment} (derivation : Derivation T (Context.empty T) claim)
    (hypotheses : ∀ i, (treeModel T).Carrier ((Context.empty T).claim i)) :
    derivation.eval (treeModel T) hypotheses = closedTree derivation := by
  induction derivation with
  | hypothesis index => exact Fin.elim0 index
  | apply rule children ih =>
    change Tree.node rule (List.ofFn (fun i => (children i).eval (treeModel T) hypotheses)) =
      Tree.node rule (List.ofFn (fun i => closedTree (children i)))
    exact congrArg (Tree.node rule) (congrArg List.ofFn (funext ih))

end Foundation.Logic.SharedInference
