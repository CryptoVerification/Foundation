import Foundation.Crypto.Logic.Polygraph.GameProofHigher
import Mathlib.Tactic.Tauto

/-! Generate transport diagrams for a code-changing implementation update.
One square per original atom is the only nonstructural generator. A diagram
for any composite plan is assembled without enumerating alternative paths.
Bridge atoms add no guards or symbolic charges in this interface. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Transport
variable {Vertex Atom Requirement Budget : Type} [DecidableEq Requirement]
set_option backward.isDefEq.respectTransparency false

inductive Label (Vertex Atom : Type) where
  | before : Atom → Label Vertex Atom
  | after : Atom → Label Vertex Atom
  | bridge : Vertex → Label Vertex Atom
  deriving DecidableEq

def layout (original : Layout Vertex Atom Requirement Budget) :
    Layout (Vertex ⊕ Vertex) (Label Vertex Atom) Requirement Budget where
  source := fun
    | Label.before label => Sum.inl (original.source label)
    | Label.after label => Sum.inr (original.source label)
    | Label.bridge vertex => Sum.inl vertex
  target := fun
    | Label.before label => Sum.inl (original.target label)
    | Label.after label => Sum.inr (original.target label)
    | Label.bridge vertex => Sum.inr vertex
  needs := fun | Label.before label | Label.after label => original.needs label | .bridge _ => ∅
  charges := fun | Label.before label | Label.after label => original.charges label | .bridge _ => 0

def before (original : Layout Vertex Atom Requirement Budget) : {a b : Vertex} →
    Plan original a b → Plan (layout original) (Sum.inl a) (Sum.inl b)
  | _, _, .identity a => .identity (Sum.inl a)
  | _, _, .atom label => .atom (Label.before label)
  | _, _, .seq first second => .seq (before original first) (before original second)

def after (original : Layout Vertex Atom Requirement Budget) : {a b : Vertex} →
    Plan original a b → Plan (layout original) (Sum.inr a) (Sum.inr b)
  | _, _, .identity a => .identity (Sum.inr a)
  | _, _, .atom label => .atom (Label.after label)
  | _, _, .seq first second => .seq (after original first) (after original second)

def bridge (original : Layout Vertex Atom Requirement Budget) (vertex : Vertex) :
    Plan (layout original) (Sum.inl vertex) (Sum.inr vertex) := .atom (Label.bridge vertex)

theorem bridge_needs (original : Layout Vertex Atom Requirement Budget) (vertex : Vertex) :
    (bridge original vertex).needs (layout original) = ∅ := rfl

theorem before_needs (original : Layout Vertex Atom Requirement Budget) {a b} (plan : Plan original a b) :
    (before original plan).needs (layout original) = plan.needs original := by
  induction plan <;> simp_all only [before, Plan.needs, layout]

theorem after_needs (original : Layout Vertex Atom Requirement Budget) {a b} (plan : Plan original a b) :
    (after original plan).needs (layout original) = plan.needs original := by
  induction plan <;> simp_all only [after, Plan.needs, layout]

def relators (original : Layout Vertex Atom Requirement Budget) (label : Atom) : Relator (layout original) where
  source := Sum.inl (original.source label)
  target := Sum.inr (original.target label)
  left := .seq (.atom (Label.before label)) (bridge original (original.target label))
  right := .seq (bridge original (original.source label)) (.atom (Label.after label))
  needs := ∅
  balanced := by simp only [Plan.charges, bridge, layout, add_zero, zero_add]

def diagram (original : Layout Vertex Atom Requirement Budget) : {a b : Vertex} → (plan : Plan original a b) →
    Cell (layout original) (relators original)
      (.seq (before original plan) (bridge original b)) (.seq (bridge original a) (after original plan))
  | _, _, .identity a => (Cell.leftUnit (bridge original a)).trans (Cell.rightUnit (bridge original a)).symm
  | _, _, .atom label => .rule label
  | a, c, .seq (b := b) first second =>
      (Cell.assoc (before original first) (before original second) (bridge original c)).trans
        ((Cell.seq (.refl (before original first)) (diagram original second)).trans
          ((Cell.assoc (before original first) (bridge original b) (after original second)).symm.trans
            ((Cell.seq (diagram original first) (.refl (after original second))).trans
              (Cell.assoc (bridge original a) (after original first) (after original second)))))

theorem diagram_needs (original : Layout Vertex Atom Requirement Budget) {a b} (plan : Plan original a b) :
    (diagram original plan).needs (layout original) (relators original) = plan.needs original := by
  induction plan with
  | identity => simp only [diagram, Cell.needs, bridge, Plan.needs, layout, Finset.union_empty]
  | atom label => simp only [diagram, Cell.needs, relators, bridge, Plan.needs, layout,
      Finset.union_empty, Finset.empty_union, Finset.union_self]
  | seq first second one two =>
      simp only [diagram, Cell.needs, one, two, before_needs, after_needs, bridge_needs, Plan.needs,
        Finset.union_empty, Finset.empty_union]
      ext label
      simp only [Finset.mem_union]
      tauto

/-- Only diagram syntax constructors are counted, excluding boundaries,
labels, code, resource proofs and the common rule library. -/
def cellCount {V A R B I : Type} [DecidableEq R] {spec : Layout V A R B} {rules : I → Relator spec} :
    {a b : V} → {p q : Plan spec a b} → Cell spec rules p q → Nat
  | _, _, _, _, .symm child => 1 + cellCount child
  | _, _, _, _, .trans first second | _, _, _, _, .seq first second => 1 + cellCount first + cellCount second
  | _, _, _, _, _ => 1

def planCount (original : Layout Vertex Atom Requirement Budget) : {a b : Vertex} → Plan original a b → Nat
  | _, _, .identity _ | _, _, .atom _ => 1
  | _, _, .seq first second => 1 + planCount original first + planCount original second

theorem diagram_count_bound (original : Layout Vertex Atom Requirement Budget) {a b} (plan : Plan original a b) :
    cellCount (diagram original plan) ≤ 12 * planCount original plan := by
  induction plan <;> simp_all only [diagram, cellCount, planCount] <;> omega

def generatorCount {V A R B I : Type} [DecidableEq R] {spec : Layout V A R B} {rules : I → Relator spec} :
    {a b : V} → {p q : Plan spec a b} → Cell spec rules p q → Nat
  | _, _, _, _, .rule _ => 1
  | _, _, _, _, .symm child => generatorCount child
  | _, _, _, _, .trans first second | _, _, _, _, .seq first second => generatorCount first + generatorCount second
  | _, _, _, _, _ => 0

def atomCount (original : Layout Vertex Atom Requirement Budget) : {a b : Vertex} → Plan original a b → Nat
  | _, _, .identity _ => 0
  | _, _, .atom _ => 1
  | _, _, .seq first second => atomCount original first + atomCount original second

theorem diagram_generator_count (original : Layout Vertex Atom Requirement Budget) {a b} (plan : Plan original a b) :
    generatorCount (diagram original plan) = atomCount original plan := by
  induction plan <;> simp_all only [diagram, generatorCount, atomCount, Nat.zero_add, Nat.add_zero, Nat.add_comm]

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Transport
