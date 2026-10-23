import Foundation.Logic.SharedInference

/-! Evaluate a finite reference certificate without unfolding it to a tree.
The homomorphism theorem proves that the numerical size evaluation equals
the size of the expanded tree, even when that tree is not materialized.
Evaluation alone does not validate arity or judgments: use `check` first. -/
namespace Foundation.Logic.SharedInference
set_option backward.isDefEq.respectTransparency false
universe j r u v
variable {T : Presentation.{j, r}} {A : Type u} {B : Type v}

def gather (cache : List A) : List Nat → Option (List A)
  | [] => some []
  | index :: indices => do
      let first ← cache[index]?
      let rest ← gather cache indices
      pure (first :: rest)

def runValues (operation : T.Rule → List A → A) : List (Node T) → List A → Option (List A)
  | [], cache => some cache
  | node :: nodes, cache => do
      let children ← gather cache node.parents
      runValues operation nodes (cache ++ [operation node.rule children])

def Certificate.eval (certificate : Certificate T) (operation : T.Rule → List A → A) : Option A := do
  let cache ← runValues operation certificate.nodes []
  cache[certificate.output]?

theorem runValues_append (operation : T.Rule → List A → A) (first second : List (Node T)) (cache : List A) :
    runValues operation (first ++ second) cache =
      (runValues operation first cache).bind (runValues operation second) := by
  induction first generalizing cache with
  | nil => rfl
  | cons node first ih =>
    simp only [List.cons_append, runValues]
    cases parents : gather cache node.parents with
    | none => rfl
    | some children =>
      change runValues operation (first ++ second) (cache ++ [operation node.rule children]) = _
      exact ih _

theorem gather_map (f : A → B) (cache : List A) (indices : List Nat) :
    gather (cache.map f) indices = (gather cache indices).map (List.map f) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp only [gather, List.getElem?_map, ih]
    cases first : cache[index]? <;> cases rest : gather cache indices <;> rfl

theorem runValues_map (source : T.Rule → List A → A) (target : T.Rule → List B → B) (f : A → B)
    (preserves : ∀ rule children, target rule (children.map f) = f (source rule children))
    (nodes : List (Node T)) (cache : List A) :
    runValues target nodes (cache.map f) = (runValues source nodes cache).map (List.map f) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node nodes ih =>
    simp only [runValues, gather_map]
    cases parents : gather cache node.parents with
    | none => rfl
    | some children =>
      change runValues target nodes (cache.map f ++ [target node.rule (children.map f)]) =
        (runValues source nodes (cache ++ [source node.rule children])).map (List.map f)
      rw [preserves]
      simpa only [List.map_append, List.map_singleton] using ih (cache ++ [source node.rule children])

theorem Certificate.eval_map (certificate : Certificate T) (source : T.Rule → List A → A)
    (target : T.Rule → List B → B) (f : A → B)
    (preserves : ∀ rule children, target rule (children.map f) = f (source rule children)) :
    certificate.eval target = (certificate.eval source).map f := by
  have mapped := runValues_map source target f preserves certificate.nodes []
  simp only [List.map_nil] at mapped
  unfold Certificate.eval
  rw [mapped]
  cases result : runValues source certificate.nodes [] with
  | none => rfl
  | some cache =>
    change (cache.map f)[certificate.output]? = (cache[certificate.output]?).map f
    exact List.getElem?_map

inductive Tree (Rule : Type r) where
  | node (rule : Rule) (children : List (Tree Rule))

def Tree.nodeCount {Rule : Type r} : Tree Rule → Nat
  | .node _ children => 1 + (children.map Tree.nodeCount).sum

def Certificate.expandedSize (certificate : Certificate T) : Option Nat :=
  certificate.eval (fun _ children => 1 + children.sum)

/-- The numerical scan is exactly a tree-size computation. It makes no
minimal-proof or runtime claim and need not allocate the expanded tree. -/
theorem Certificate.expandedSize_correct (certificate : Certificate T) :
    certificate.expandedSize = (certificate.eval Tree.node).map Tree.nodeCount :=
  certificate.eval_map Tree.node (fun _ children => 1 + children.sum) Tree.nodeCount (fun _ _ => by rw [Tree.nodeCount])

end Foundation.Logic.SharedInference
