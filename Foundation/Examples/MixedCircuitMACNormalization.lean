import Foundation.Examples.MixedCircuitMACRoots
import Foundation.Crypto.Logic.Polygraph.MixedCircuitNormalization

/-! Executable MAC-root selection and normalization in arbitrary mixed
contexts. The catalogue rewrites preparation followed by elimination; pure
wiring values are frozen. No structural coherence or native cost is inferred. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

/-- A positive root-pattern view, not a full equality test for circuits.
Wire/tensor internals cannot match a two-box MAC redex. -/
inductive RootShape where
  | other
  | box (label : MACNormalization.Atom)
  | seq (left right : RootShape)

def rootShape : {n m : Port signature} → Circuit signature n m → RootShape
  | _, _, .box label => .box label
  | _, _, .seq left right => .seq (rootShape left) (rootShape right)
  | _, _, _ => .other

def beforeShape (stage : Nat) : RootShape := .seq (.box (.schedule stage)) (.box (.eliminate stage))

def detect : (shape : RootShape) → Option {stage : Nat // shape = beforeShape stage}
  | .seq (.box (.schedule stage)) (.box (.eliminate other)) =>
      if same : stage = other then by cases same; exact some ⟨stage, rfl⟩ else none
  | _ => none

def packed {n m : Port signature} (circuit : Circuit signature n m) :
    Σ n m : Port signature, Circuit signature n m := ⟨n, m, circuit⟩

theorem box_shape {n m} (circuit : Circuit signature n m) (label : MACNormalization.Atom)
    (same : rootShape circuit = .box label) : packed circuit = packed (Circuit.box (signature := signature) label) := by
  cases circuit with
  | box other => cases same; rfl
  | wire => cases same
  | seq => cases same
  | tensor => cases same

theorem before_shape {n m} (circuit : Circuit signature n m) (stage : Nat)
    (same : rootShape circuit = beforeShape stage) : packed circuit = packed (before stage) := by
  cases circuit with
  | seq left right =>
      have pieces := RootShape.seq.inj same
      have one := box_shape left (.schedule stage) pieces.1
      have two := box_shape right (.eliminate stage) pieces.2
      cases one
      cases two
      rfl
  | wire => cases same
  | box => cases same
  | tensor => cases same

/-- A positive pattern match is accompanied by typed reconstruction. -/
def rootAt {n m : Port signature} (circuit : Circuit signature n m) :
    Option (Σ target, Primitive relators circuit target) :=
  match detect (rootShape circuit) with
  | none => none
  | some ⟨stage, sameShape⟩ => by
      have same := before_shape circuit stage sameShape
      cases same
      exact some ⟨after stage, .rule stage⟩

theorem rootAt_complete {n m} {a b : Circuit signature n m} (primitive : Primitive relators a b) :
    (rootAt a).isSome = true := by
  cases primitive with
  | rule stage => simp [rootAt, detect, rootShape, beforeShape, relators, before]

/-- Select a root if present, otherwise search the left then right child.
The returned data contains an actual typed rewrite, not just an index. -/
def next : {n m : Port signature} → (circuit : Circuit signature n m) →
    Option (Σ target, Step relators circuit target)
  | _, _, .wire _ => none
  | _, _, .box _ => none
  | _, _, .seq left right =>
      match rootAt (.seq left right) with
      | some ⟨target, primitive⟩ => some ⟨target, .root primitive⟩
      | none =>
          match next left with
          | some ⟨target, change⟩ => some ⟨.seq target right, .seqLeft change right⟩
          | none =>
              match next right with
              | some ⟨target, change⟩ => some ⟨.seq left target, .seqRight left change⟩
              | none => none
  | _, _, .tensor left right =>
      match next left with
      | some ⟨target, change⟩ => some ⟨.tensor target right, .tensorLeft change right⟩
      | none =>
          match next right with
          | some ⟨target, change⟩ => some ⟨.tensor left target, .tensorRight left change⟩
          | none => none

theorem next_complete {n m} {a b : Circuit signature n m} (change : Step relators a b) : next a ≠ none := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule stage => simp [next, rootAt, detect, rootShape, beforeShape, before, relators]
  | seqLeft child fixed ih =>
      simp only [next]
      cases rootAt (Circuit.seq _ fixed) with
      | some selected => cases selected; simp
      | none => cases result : next _ with
        | some selected => cases selected; simp
        | none => exact False.elim (ih result)
  | seqRight fixed child ih =>
      simp only [next]
      cases rootAt (Circuit.seq fixed _) with
      | some selected => cases selected; simp
      | none => cases next fixed with
        | some selected => cases selected; simp
        | none => cases result : next _ with
          | some selected => cases selected; simp
          | none => exact False.elim (ih result)
  | tensorLeft child fixed ih =>
      simp only [next]
      cases result : next _ with
      | some selected => cases selected; simp
      | none => exact False.elim (ih result)
  | tensorRight fixed child ih =>
      simp only [next]
      cases next fixed with
      | some selected => cases selected; simp
      | none => cases result : next _ with
        | some selected => cases selected; simp
        | none => exact False.elim (ih result)

def normalizationStrategy : Strategy relators where
  rank := boxCount
  decreases := by
    intro n m a b change
    have equality := step_count change
    omega
  select circuit :=
    match selected : next circuit with
    | none => .done (fun change => next_complete change selected)
    | some ⟨_, change⟩ => .more change

def normalForm {n m} (circuit : Circuit signature n m) := normalize normalizationStrategy circuit

theorem path_count {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) :
    boxCount b + path.length = boxCount a := by
  induction path with
  | refl => simp only [RewritePath.length, Nat.add_zero]
  | cons change tail ih =>
      have one := step_count change
      simp only [RewritePath.length]
      omega

theorem normal_length {n m} (circuit : Circuit signature n m) :
    (normalForm circuit).path.length ≤ boxCount circuit := by
  have counted := path_count (normalForm circuit).path
  omega

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
