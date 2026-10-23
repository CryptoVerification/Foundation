import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Multiset.AddSub

/-! Pure, directed game-proof syntax with declared condition IDs and symbolic
error charges. Metadata never evaluates a PMF. A charge is a multiset, so
reusing one statistical assumption twice counts its error twice. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Vertex Atom Requirement Budget : Type} [DecidableEq Requirement]

structure Layout (Vertex Atom Requirement Budget : Type) where
  source : Atom → Vertex
  target : Atom → Vertex
  needs : Atom → Finset Requirement
  charges : Atom → Multiset Budget

inductive Plan (layout : Layout Vertex Atom Requirement Budget) : Vertex → Vertex → Type where
  | identity (vertex : Vertex) : Plan layout vertex vertex
  | atom (label : Atom) : Plan layout (layout.source label) (layout.target label)
  | seq {a b c} : Plan layout a b → Plan layout b c → Plan layout a c

def Plan.needs (layout : Layout Vertex Atom Requirement Budget) : {a b : Vertex} → Plan layout a b → Finset Requirement
  | _, _, .identity _ => ∅
  | _, _, .atom label => layout.needs label
  | _, _, .seq first second => first.needs layout ∪ second.needs layout

def Plan.charges (layout : Layout Vertex Atom Requirement Budget) : {a b : Vertex} → Plan layout a b → Multiset Budget
  | _, _, .identity _ => 0
  | _, _, .atom label => layout.charges label
  | _, _, .seq first second => first.charges layout + second.charges layout

/-- Holds is a proposition about named, explicitly declared conditions. -/
def Holds (condition : Requirement → Prop) (needed : Finset Requirement) : Prop :=
  ∀ label ∈ needed, condition label

omit [DecidableEq Requirement] in
theorem Holds.restrict {condition : Requirement → Prop} {one two : Finset Requirement}
    (valid : Holds condition two) (included : one ⊆ two) : Holds condition one :=
  fun label member => valid label (included member)

def fresh (needed changed : Finset Requirement) : Finset Requirement := needed ∩ changed

def checkReuse (needed changed : Finset Requirement) : Bool := decide (fresh needed changed = ∅)

/-- Old proofs transfer outside the declared change set; fresh proofs are
required only for the intersection. The transfer premise is explicit. -/
theorem repair {old updated : Requirement → Prop} {needed changed : Finset Requirement}
    (cached : Holds old needed)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh needed changed)) : Holds updated needed := by
  intro label member
  by_cases edited : label ∈ changed
  · exact rechecked label (Finset.mem_inter.mpr ⟨member, edited⟩)
  · exact unchanged label edited (cached label member)

theorem reuse {old updated : Requirement → Prop} {needed changed : Finset Requirement}
    (cached : Holds old needed)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (accepted : checkReuse needed changed = true) : Holds updated needed := by
  apply repair cached unchanged
  intro label member
  have empty : fresh needed changed = ∅ := of_decide_eq_true accepted
  rw [empty] at member
  exact False.elim (Finset.notMem_empty label member)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
