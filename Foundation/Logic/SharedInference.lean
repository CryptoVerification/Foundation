import Foundation.Logic.Presentation
import Mathlib.Data.List.OfFn

/-! Finite inference certificates with backward references. The checker sees
only rule data and natural-number references, not semantic proof arguments.
Any proof-relevant model of the rule presentation is sound for an accepted
certificate. Sharing is available to every model, including ordinary logic.
Counts below describe explicit certificate data, not kernel proof-term size
or a constant-time implementation of arbitrary rule/judgment operations. -/
namespace Foundation.Logic.SharedInference
universe j r v
variable {T : Presentation.{j, r}}

structure Node (T : Presentation.{j, r}) where
  rule : T.Rule
  parents : List Nat

structure Certificate (T : Presentation.{j, r}) where
  nodes : List (Node T)
  output : Nat

def parentsValid [DecidableEq T.Judgment] (cache : List T.Judgment) : List Nat → List T.Judgment → Bool
  | [], [] => true
  | parent :: parents, claim :: claims => decide (cache[parent]? = some claim) && parentsValid cache parents claims
  | _, _ => false

def run [DecidableEq T.Judgment] : List (Node T) → List T.Judgment → Option (List T.Judgment)
  | [], cache => some cache
  | node :: nodes, cache =>
      if parentsValid cache node.parents (List.ofFn (T.premise node.rule)) then
        run nodes (cache ++ [T.conclusion node.rule])
      else none

def check [DecidableEq T.Judgment] (certificate : Certificate T) : Option T.Judgment := do
  let cache ← run certificate.nodes []
  cache[certificate.output]?

theorem run_append [DecidableEq T.Judgment] (first second : List (Node T)) (cache : List T.Judgment) :
    run (first ++ second) cache = (run first cache).bind (run second) := by
  induction first generalizing cache with
  | nil => rfl
  | cons node first ih =>
    simp only [List.cons_append, run]
    split <;> simp_all

theorem parentsValid_sound [DecidableEq T.Judgment] {cache : List T.Judgment} {parents claims}
    (accepted : parentsValid cache parents claims = true) (property : T.Judgment → Prop)
    (known : ∀ claim ∈ cache, property claim) : ∀ claim ∈ claims, property claim := by
  induction parents generalizing claims with
  | nil => cases claims <;> simp_all [parentsValid]
  | cons parent parents ih =>
    cases claims with
    | nil => simp [parentsValid] at accepted
    | cons first rest =>
      simp only [parentsValid, Bool.and_eq_true, decide_eq_true_eq] at accepted
      intro claim member
      rcases List.mem_cons.mp member with same | later
      · subst claim
        exact known first (List.mem_of_getElem? accepted.1)
      · exact ih accepted.2 claim later

def Valid (model : Model.{j, r, v} T) (cache : List T.Judgment) : Prop :=
  ∀ claim ∈ cache, Nonempty (model.Carrier claim)

theorem node_sound [DecidableEq T.Judgment] (model : Model.{j, r, v} T) (node : Node T)
    {cache : List T.Judgment} (known : Valid model cache)
    (accepted : parentsValid cache node.parents (List.ofFn (T.premise node.rule)) = true) :
    Nonempty (model.Carrier (T.conclusion node.rule)) := by
  have premises := parentsValid_sound accepted (fun claim => Nonempty (model.Carrier claim)) known
  exact ⟨model.operation node.rule (fun i => Classical.choice
    (premises (T.premise node.rule i) (List.mem_ofFn.mpr ⟨i, rfl⟩)))⟩

theorem run_sound [DecidableEq T.Judgment] (model : Model.{j, r, v} T)
    {nodes : List (Node T)} {cache result : List T.Judgment} (known : Valid model cache)
    (accepted : run nodes cache = some result) : Valid model result := by
  induction nodes generalizing cache with
  | nil => simp only [run, Option.some.injEq] at accepted; subst result; exact known
  | cons node nodes ih =>
    simp only [run] at accepted
    split at accepted
    next valid =>
      apply ih _ accepted
      intro claim member
      rcases List.mem_append.mp member with previous | fresh
      · exact known claim previous
      · have same := List.mem_singleton.mp fresh
        subst claim
        exact node_sound model node known valid
    next => contradiction

theorem sound [DecidableEq T.Judgment] (model : Model.{j, r, v} T) (certificate : Certificate T)
    {claim : T.Judgment} (accepted : check certificate = some claim) : Nonempty (model.Carrier claim) := by
  cases result : run certificate.nodes [] with
  | none => simp [check, result] at accepted
  | some cache =>
    have known := run_sound model (cache := []) (by intro _ member; cases member) result
    have lookup : cache[certificate.output]? = some claim := by simpa [check, result] using accepted
    exact known claim (List.mem_of_getElem? lookup)

def Certificate.nodeCount (certificate : Certificate T) : Nat := certificate.nodes.length

def Certificate.referenceCount (certificate : Certificate T) : Nat :=
  (certificate.nodes.map (fun node => node.parents.length)).sum

/-- Successful lookup of index i in the current linked-list checker visits
i+1 entries. This counts reference traversals, excluding equality tests,
cache append, rule construction, and semantic proof checking. -/
def Certificate.lookupSteps (certificate : Certificate T) : Nat :=
  (certificate.nodes.map (fun node => (node.parents.map (· + 1)).sum)).sum

/-- Rule payloads are charged explicitly by a caller-chosen measure. In an
application this must include boundary plans and local-rule arguments. -/
def Certificate.payloadCost (certificate : Certificate T) (weight : T.Rule → Nat) : Nat :=
  (certificate.nodes.map (fun node => weight node.rule)).sum

/-- Serialize all rule payloads and reference indices. The renderer's format
and the shared local-lemma library must be accounted for by the experiment.
This function makes no injectivity assertion about an arbitrary renderer. -/
def Certificate.encode (certificate : Certificate T) (render : T.Rule → String) : String :=
  "[" ++ String.intercalate "," (certificate.nodes.map fun node =>
    "(" ++ render node.rule ++ ";[" ++ String.intercalate "," (node.parents.map toString) ++ "])") ++
    "];" ++ toString certificate.output

end Foundation.Logic.SharedInference
