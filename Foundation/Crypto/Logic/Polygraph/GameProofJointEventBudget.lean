import Foundation.Crypto.Logic.Polygraph.GameProofRequirements
import Foundation.Crypto.Semantics.Probability.SharedEventBudget

/-! Joint realization of a game diagram off named bad events. All vertices
are functions of the same World. Pairwise couplings or repeated text labels
alone are insufficient premises for this accounting rule. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.JointEventBudget
open Foundation.Probability
open scoped ENNReal BigOperators
variable {Vertex Atom Requirement Budget World Value : Type}
variable [DecidableEq Budget]
set_option backward.isDefEq.respectTransparency false

structure Realization (layout : Layout Vertex Atom Requirement Budget) (World Value : Type) where
  value : Vertex → World → Value
  bad : Budget → World → Prop
  root : ∀ label world, (∀ charge ∈ layout.charges label, ¬bad charge world) →
    value (layout.source label) world = value (layout.target label) world

omit [DecidableEq Budget] in
theorem Realization.plan {layout : Layout Vertex Atom Requirement Budget} (model : Realization layout World Value)
    {a b : Vertex} (p : Plan layout a b) (world : World)
    (good : ∀ charge ∈ p.charges layout, ¬model.bad charge world) : model.value a world = model.value b world := by
  induction p with
  | identity => rfl
  | atom label => exact model.root label world good
  | seq first second ih₁ ih₂ =>
      exact (ih₁ (fun charge member => good charge (Multiset.mem_add.mpr (Or.inl member)))).trans
        (ih₂ (fun charge member => good charge (Multiset.mem_add.mpr (Or.inr member))))

structure Request (layout : Layout Vertex Atom Requirement Budget) where
  source : Vertex
  target : Vertex
  path : Plan layout source target

noncomputable def support {Index : Type} [Fintype Index] {layout : Layout Vertex Atom Requirement Budget}
    (requests : Index → Request layout) : Finset Budget :=
  Finset.univ.biUnion (fun index => ((requests index).path.charges layout).toFinset)

def failure {Index : Type} {layout : Layout Vertex Atom Requirement Budget} (model : Realization layout World Value)
    (requests : Index → Request layout) (world : World) : Prop :=
  ∃ index, model.value (requests index).source world ≠ model.value (requests index).target world

theorem failure_covered {Index : Type} [Fintype Index] {layout : Layout Vertex Atom Requirement Budget}
    (model : Realization layout World Value) (requests : Index → Request layout) (world : World) :
    failure model requests world → SharedEventBudget.occurs model.bad (support requests) world := by
  classical
  intro failed
  by_contra safe
  obtain ⟨index, different⟩ := failed
  apply different
  apply model.plan (requests index).path world
  intro charge member bad
  apply safe
  exact ⟨charge, Finset.mem_biUnion.mpr ⟨index, Finset.mem_univ _, Multiset.mem_toFinset.mpr member⟩, bad⟩

theorem family_bound {Index : Type} [Fintype Index] {layout : Layout Vertex Atom Requirement Budget}
    (model : Realization layout World Value) (requests : Index → Request layout) (law : ProbComp World)
    (price : Budget → ℝ≥0∞)
    (localBound : ∀ charge ∈ support requests, eventProb law (model.bad charge) ≤ price charge) :
    eventProb law (failure model requests) ≤ SharedEventBudget.budget price (support requests) :=
  SharedEventBudget.covers law model.bad (support requests) (failure model requests)
    (failure_covered model requests) price localBound

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.JointEventBudget
