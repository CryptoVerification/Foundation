import Foundation.Crypto.Logic.Polygraph.GameProofRequirements

/-! A finite structural encoding of directed plans. Decoding checks every
intermediate vertex, so syntactic equality is executable even for indexed
plans. No proof term, PMF, or semantic equivalence test is encoded. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Vertex Atom Requirement Budget : Type}
set_option backward.isDefEq.respectTransparency false

inductive PlanShape (Vertex Atom : Type) where
  | identity (vertex : Vertex)
  | atom (label : Atom)
  | seq (first second : PlanShape Vertex Atom)
  deriving DecidableEq, Repr

def Plan.shape {layout : Layout Vertex Atom Requirement Budget} : {a b : Vertex} → Plan layout a b → PlanShape Vertex Atom
  | _, _, .identity vertex => .identity vertex
  | _, _, .atom label => .atom label
  | _, _, .seq first second => .seq first.shape second.shape

abbrev PackedPlan (layout : Layout Vertex Atom Requirement Budget) := Σ a b, Plan layout a b

def PlanShape.decode [DecidableEq Vertex] (layout : Layout Vertex Atom Requirement Budget) :
    PlanShape Vertex Atom → Option (PackedPlan layout)
  | .identity vertex => some ⟨vertex, vertex, .identity vertex⟩
  | .atom label => some ⟨layout.source label, layout.target label, .atom label⟩
  | .seq first second => do
      let first ← first.decode layout
      let second ← second.decode layout
      if agrees : first.2.1 = second.1 then
        let joinedFirst : Plan layout first.1 second.1 := agrees ▸ first.2.2
        pure ⟨first.1, second.2.1, .seq joinedFirst second.2.2⟩
      else none

theorem Plan.decode_shape [DecidableEq Vertex] {layout : Layout Vertex Atom Requirement Budget}
    {a b : Vertex} (plan : Plan layout a b) : plan.shape.decode layout = some ⟨a, b, plan⟩ := by
  induction plan with
  | identity => rfl
  | atom => rfl
  | seq first second ihFirst ihSecond => simp [Plan.shape, PlanShape.decode, ihFirst, ihSecond]

theorem Plan.shape_injective [DecidableEq Vertex] {layout : Layout Vertex Atom Requirement Budget}
    {a b : Vertex} {first second : Plan layout a b} (same : first.shape = second.shape) : first = second := by
  have decoded := congrArg (PlanShape.decode layout) same
  rw [first.decode_shape, second.decode_shape, Option.some.injEq] at decoded
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using decoded

instance [DecidableEq Vertex] [DecidableEq Atom] {layout : Layout Vertex Atom Requirement Budget} {a b : Vertex} :
    DecidableEq (Plan layout a b) := fun first second =>
  if same : first.shape = second.shape then isTrue (Plan.shape_injective same)
  else isFalse (fun equal => same (congrArg Plan.shape equal))

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
