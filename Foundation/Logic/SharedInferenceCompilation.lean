import Foundation.Logic.SharedInferenceEvaluation

/-! Untrusted structural interning followed by the proved inference checker.
Identical rules with identical parent indices share one row. Fuel makes the
producer total; failures are explicit. Soundness does not trust the producer,
the deduplication strategy, or equality of a mere text rendering. -/
namespace Foundation.Logic.SharedInference
universe j r
variable {T : Presentation.{j, r}}
set_option backward.isDefEq.respectTransparency false

def intern [DecidableEq T.Rule] (rule : T.Rule) (parents : List Nat) (cache : List (Node T)) : Nat × List (Node T) :=
  match cache.findIdx? (fun node => decide (node.rule = rule ∧ node.parents = parents)) with
  | some index => (index, cache)
  | none => (cache.length, cache ++ [⟨rule, parents⟩])

def compileFuel [DecidableEq T.Rule] (sharing : Bool) : Nat → Tree T.Rule → List (Node T) → Option (Nat × List (Node T))
  | 0, _, _ => none
  | fuel + 1, .node rule children, cache => do
      let (parents, cache) ← children.foldlM (fun (state : List Nat × List (Node T)) child => do
        let (index, updated) ← compileFuel sharing fuel child state.2
        pure (state.1 ++ [index], updated)) ([], cache)
      pure (if sharing then intern rule parents cache else (cache.length, cache ++ [⟨rule, parents⟩]))

def compile [DecidableEq T.Rule] (tree : Tree T.Rule) : Option (Certificate T) := do
  let (output, nodes) ← compileFuel true (tree.nodeCount + 1) tree []
  pure ⟨nodes, output⟩

def compileUnshared [DecidableEq T.Rule] (tree : Tree T.Rule) : Option (Certificate T) := do
  let (output, nodes) ← compileFuel false (tree.nodeCount + 1) tree []
  pure ⟨nodes, output⟩

def compileChecked [DecidableEq T.Rule] [DecidableEq T.Judgment]
    (tree : Tree T.Rule) (expected : T.Judgment) : Option (Certificate T) := do
  let certificate ← compile tree
  if check certificate = some expected then pure certificate else none

theorem compileChecked_accepts [DecidableEq T.Rule] [DecidableEq T.Judgment]
    (tree : Tree T.Rule) (expected : T.Judgment) {certificate : Certificate T}
    (produced : compileChecked tree expected = some certificate) : check certificate = some expected := by
  cases result : compile tree with
  | none => simp [compileChecked, result] at produced
  | some candidate =>
    unfold compileChecked at produced
    rw [result] at produced
    change (if check candidate = some expected then some candidate else none) = some certificate at produced
    by_cases accepted : check candidate = some expected
    · rw [if_pos accepted] at produced
      have same : candidate = certificate := Option.some.inj produced
      subst candidate
      exact accepted
    · rw [if_neg accepted] at produced
      contradiction

theorem compileChecked_sound [DecidableEq T.Rule] [DecidableEq T.Judgment]
    (model : Model T) (tree : Tree T.Rule) (expected : T.Judgment) {certificate : Certificate T}
    (produced : compileChecked tree expected = some certificate) : Nonempty (model.Carrier expected) :=
  sound model certificate (compileChecked_accepts tree expected produced)

end Foundation.Logic.SharedInference
