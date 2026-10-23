import Foundation.Crypto.Semantics.Probability.SelectedCouplingTags

/-! Executable supplied-cut repair certificates for selected couplings.
The checker validates a requested edge change and a weighted budget. The
repair is computed from the supplied cut, not selected by classical choice.
No optimal-cut search or proof-size advantage is asserted. -/
namespace Foundation.Probability.SelectedCouplingGraph.Certificate
open Graph
set_option backward.isDefEq.respectTransparency false
variable {Vertex Edge : Type} (G : Graph Vertex Edge)

structure Repair (Vertex : Type) where
  cut : Vertex → Bool

def repaired (original : Vertex → Bool) (certificate : Repair Vertex) : Edge → Bool :=
  G.boundary (shifted original certificate.cut)

variable [Fintype Edge]

def validates (weight : Edge → Nat) (locked : Edge) (budget : Nat) (certificate : Repair Vertex) : Bool :=
  decide (certificate.cut (G.source locked) ≠ certificate.cut (G.target locked) ∧
    G.cutCost weight certificate.cut ≤ budget)

theorem validates_iff (weight : Edge → Nat) (locked : Edge) (budget : Nat) (certificate : Repair Vertex) :
    validates G weight locked budget certificate = true ↔
      certificate.cut (G.source locked) ≠ certificate.cut (G.target locked) ∧
      G.cutCost weight certificate.cut ≤ budget := by
  simp only [validates, decide_eq_true_eq]

theorem sound (width : Nat) (original : Vertex → Bool) (weight : Edge → Nat)
    (locked : Edge) (budget : Nat) (certificate : Repair Vertex)
    (accepted : validates G weight locked budget certificate = true) :
    (∃ candidate, TagRealizes G (width + 1) (repaired G original certificate) candidate) ∧
    repaired G original certificate locked ≠ G.boundary original locked ∧
    repairCost weight (G.boundary original) (repaired G original certificate) ≤ budget := by
  obtain ⟨separated, bounded⟩ := (validates_iff G weight locked budget certificate).mp accepted
  exact ⟨(tag_selected_joint_iff G width _).mpr ⟨shifted original certificate.cut, rfl⟩,
    (G.shifted_changed_iff original certificate.cut locked).mpr separated,
    (G.shifted_cost weight original certificate.cut).trans_le bounded⟩

omit [Fintype Edge] in
theorem unchanged (original : Vertex → Bool) (certificate : Repair Vertex) (edge : Edge)
    (outside : certificate.cut (G.source edge) = certificate.cut (G.target edge)) :
    repaired G original certificate edge = G.boundary original edge := by
  apply Classical.byContradiction
  intro changed
  exact ((G.shifted_changed_iff original certificate.cut edge).mp changed) outside

/-- Every feasible repair within the budget admits a checked certificate.
This completeness theorem does not itself search for the certificate. -/
theorem complete (width : Nat) (original : Vertex → Bool) (weight : Edge → Nat)
    (locked : Edge) (budget : Nat) :
    (∃ certificate, validates G weight locked budget certificate = true) ↔
    (∃ updated, ∃ candidate, TagRealizes G (width + 1) updated candidate ∧
      updated locked ≠ G.boundary original locked ∧
      repairCost weight (G.boundary original) updated ≤ budget) := by
  constructor
  · rintro ⟨certificate, accepted⟩
    obtain ⟨⟨candidate, realizes⟩, changed, bounded⟩ := sound G width original weight locked budget certificate accepted
    exact ⟨repaired G original certificate, candidate, realizes, changed, bounded⟩
  · rintro ⟨updated, candidate, realizes, changed, bounded⟩
    obtain ⟨cut, separated, price⟩ := (tag_repair_cost_iff G width weight original locked
      (repairCost weight (G.boundary original) updated)).mp ⟨updated, candidate, realizes, changed, rfl⟩
    exact ⟨⟨cut⟩, (validates_iff G weight locked budget ⟨cut⟩).mpr ⟨separated, price.trans_le bounded⟩⟩

end Foundation.Probability.SelectedCouplingGraph.Certificate
