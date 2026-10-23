import Foundation.Logic.SharedInferenceEvaluation
import Foundation.Examples.GameProofMACNormalization

/-! A controlled sharing experiment using an actual retained-state MAC local
comparison. The very same finite reference certificate is interpreted as a
higher diagram or as ordinary kernel/loss equalities. Repeated doubling is a
stress family, not a minimal cryptographic proof: a one-node reflexivity
certificate also proves the final boundary in both interpretations. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.SharedMAC
open Foundation.Logic
open Foundation.Logic.SharedInference
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

inductive Rule where
  | root
  | refl (route : Bool)
  | symm (first second : Bool)
  | trans (first middle last : Bool)
  deriving DecidableEq, Repr

abbrev theory : Presentation where
  Judgment := Bool × Bool
  Rule := Rule
  arity := fun | .root | .refl _ => 0 | .symm .. => 1 | .trans .. => 2
  premise := fun
    | .root | .refl _ => Fin.elim0
    | .symm first second => fun _ => (first, second)
    | .trans first middle last => Fin.cases (first, middle) (fun _ => (middle, last))
  conclusion := fun
    | .root => (false, true)
    | .refl route => (route, route)
    | .symm first second => (second, first)
    | .trans first _ last => (first, last)

def route (stage : Nat) : Bool → Plan MACNormalization.layout (.stage (stage + 1)) .finish
  | false => .seq (.atom (MACNormalization.Atom.schedule stage)) (.atom (MACNormalization.Atom.eliminate stage))
  | true => MACNormalization.direct (stage + 1)

def geometric (stage : Nat) : Foundation.Logic.Model theory where
  Carrier := fun claim => Cell MACNormalization.layout MACNormalization.relators (route stage claim.1) (route stage claim.2)
  operation := fun rule children => match rule with
    | .root => .rule stage
    | .refl choice => .refl (route stage choice)
    | .symm _ _ => .symm (children 0)
    | .trans _ _ _ => .trans (children 0) (children 1)

noncomputable def realization (orders : Nat → Schedule 8) (stage : Nat) (choice : Bool) :=
  evaluate (MACNormalization.baseModel orders) (route stage choice) (MACNormalization.conditions orders _)

/-- This cache stores ordinary propositions about conditional kernels and
assigned losses. It does not store a syntactic Cell or enumerate paths. -/
noncomputable def ordinary (orders : Nat → Schedule 8) (stage : Nat) : Foundation.Logic.Model theory where
  Carrier := fun claim => Comparison (realization orders stage claim.1) (realization orders stage claim.2)
  operation := fun rule children => match rule with
    | .root => ((MACNormalization.model orders).comparison stage
        (MACNormalization.conditions orders _) (MACNormalization.conditions orders _) (MACNormalization.conditions orders _)).sound
    | .refl _ => ⟨fun _ => rfl, rfl⟩
    | .symm _ _ => ⟨fun state => ((children 0).kernel_eq state).symm, (children 0).loss_eq.symm⟩
    | .trans _ _ _ => ⟨fun state => ((children 0).kernel_eq state).trans ((children 1).kernel_eq state),
        (children 0).loss_eq.trans (children 1).loss_eq⟩

/-- Every geometric value can be erased to the ordinary comparison, using
the same checked local MAC model. No new game equivalence is assumed. -/
noncomputable def erasure (orders : Nat → Schedule 8) (stage : Nat) :
    Foundation.Logic.Model.Hom (geometric stage) (ordinary orders stage) where
  map _ cell := evaluateCell_sound (MACNormalization.model orders) cell (MACNormalization.conditions orders _)
  preserves _ _ := Subsingleton.elim _ _

def nodes : Nat → List (Node theory)
  | 0 => [⟨.root, []⟩, ⟨.symm false true, [0]⟩, ⟨.trans false true false, [0, 1]⟩]
  | n + 1 => nodes n ++ [⟨.trans false false false, [n + 2, n + 2]⟩]

def certificate (n : Nat) : Certificate theory := ⟨nodes n, n + 2⟩

def claims (n : Nat) : List (Bool × Bool) :=
  [(false, true), (true, false)] ++ List.replicate (n + 1) (false, false)

theorem claims_last (n : Nat) : (claims n)[n + 2]? = some (false, false) := by
  simp [claims]

theorem claims_succ (n : Nat) : claims (n + 1) = claims n ++ [(false, false)] := by
  simp only [claims, List.replicate_succ', List.append_assoc]

theorem run_nodes (n : Nat) : run (nodes n) [] = some (claims n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nodes, run_append (T := theory), ih]
    change (if parentsValid (T := theory) (claims n) [n + 2, n + 2] [(false, false), (false, false)] then
      some (claims n ++ [(false, false)]) else none) = some (claims (n + 1))
    simp only [parentsValid, claims_last, decide_true, Bool.true_and, if_true, ← claims_succ]

theorem accepted (n : Nat) : check (certificate n) = some (false, false) := by
  change (run (nodes n) []).bind (fun cache => cache[n + 2]?) = _
  rw [run_nodes]
  exact claims_last n

theorem higher_certificate (stage n : Nat) :
    Nonempty (Cell MACNormalization.layout MACNormalization.relators (route stage false) (route stage false)) :=
  sound (geometric stage) (certificate n) (accepted n)

theorem ordinary_certificate (orders : Nat → Schedule 8) (stage n : Nat) :
    Comparison (realization orders stage false) (realization orders stage false) := by
  exact (sound (ordinary orders stage) (certificate n) (accepted n)).some

theorem node_count (n : Nat) : (certificate n).nodeCount = n + 3 := by
  change (nodes n).length = n + 3
  induction n with
  | zero => rfl
  | succ n ih => simp only [nodes, List.length_append, List.length_singleton, ih]

theorem reference_count (n : Nat) : (certificate n).referenceCount = 2 * n + 3 := by
  change ((nodes n).map (fun node => node.parents.length)).sum = _
  induction n with
  | zero => rfl
  | succ n ih => simp only [nodes, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, List.length_cons, List.length_nil, ih]; omega

theorem lookup_steps (n : Nat) : (certificate n).lookupSteps = n * n + 5 * n + 4 := by
  change ((nodes n).map (fun node => (node.parents.map (· + 1)).sum)).sum = _
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nodes, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih, Nat.add_mul, Nat.mul_add]
    omega

def expandedNodes : Nat → Nat
  | 0 => 4
  | n + 1 => 1 + 2 * expandedNodes n

def sizeCache : Nat → List Nat
  | 0 => [1, 2, 4]
  | n + 1 => sizeCache n ++ [expandedNodes (n + 1)]

theorem sizeCache_length (n : Nat) : (sizeCache n).length = n + 3 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sizeCache, List.length_append, List.length_singleton, ih]

theorem sizeCache_last (n : Nat) : (sizeCache n)[n + 2]? = some (expandedNodes n) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (sizeCache n ++ [expandedNodes (n + 1)])[n + 3]? = _
    rw [← sizeCache_length]
    exact List.getElem?_concat_length

theorem run_sizes (n : Nat) : runValues (fun (_ : Rule) children => 1 + children.sum) (nodes n) [] = some (sizeCache n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nodes, runValues_append (T := theory), ih]
    change runValues (T := theory) (fun (_ : Rule) children => 1 + children.sum)
      [⟨.trans false false false, [n + 2, n + 2]⟩] (sizeCache n) = some (sizeCache (n + 1))
    simp only [runValues, gather, sizeCache_last]
    change some (sizeCache n ++ [1 + (expandedNodes n + (expandedNodes n + 0))]) =
      some (sizeCache n ++ [expandedNodes (n + 1)])
    rw [expandedNodes, two_mul]
    rfl

theorem expanded_count (n : Nat) : (certificate n).expandedSize = some (expandedNodes n) := by
  change (runValues (fun (_ : Rule) children => 1 + children.sum) (nodes n) []).bind (fun cache => cache[n + 2]?) = _
  rw [run_sizes]
  exact sizeCache_last n

theorem expanded_closed (n : Nat) : expandedNodes n + 1 = 5 * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [expandedNodes, Nat.pow_succ]; omega

def reflexive : Certificate theory := ⟨[⟨.refl false, []⟩], 0⟩

theorem reflexive_accepted : check reflexive = some (false, false) := rfl

theorem reflexive_size : reflexive.nodeCount = 1 ∧ reflexive.referenceCount = 0 := ⟨rfl, rfl⟩

def render : Rule → String
  | .root => "R"
  | .refl route => "I" ++ toString route
  | .symm first second => "S" ++ toString first ++ ":" ++ toString second
  | .trans first middle last => "T" ++ toString first ++ ":" ++ toString middle ++ ":" ++ toString last

/-- Both interpretations consume exactly this shared input, including all
rule parameters, decimal parent indices, and the output index. The common
local-lemma library and semantic game parameters are external to this input. -/
def encodedBytes (n : Nat) : Nat := ((certificate n).encode render).utf8ByteSize

/-- info: [(0, 3, 3, some 4), (1, 4, 5, some 9), (4, 7, 11, some 79), (16, 19, 35, some 327679), (64, 67, 131, some 92233720368547758079)] -/
#guard_msgs (whitespace := lax) in
#eval [0, 1, 4, 16, 64].map (fun n => (n, (certificate n).nodeCount, (certificate n).referenceCount,
  (certificate n).expandedSize))

/-- info: (none, none, none) -/
#guard_msgs in
#eval (check (⟨[⟨Rule.root, [0]⟩], 0⟩ : Certificate theory),
  check (⟨[⟨Rule.symm false true, [0]⟩], 0⟩ : Certificate theory),
  check (⟨[⟨Rule.root, []⟩, ⟨Rule.symm true false, [0]⟩], 1⟩ : Certificate theory))

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.SharedMAC
