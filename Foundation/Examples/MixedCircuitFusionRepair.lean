import Foundation.Examples.MixedCircuitFusionProjection

/-! Relative coherence and guard-cache reuse across the conservative fusion
extension. An old comparison is an explicit input, not a coherence oracle.
No whole-presentation coherence or checking-time claim is made. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
open Foundation.Logic.Polygraph
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

noncomputable def macModel (orders : Nat → Schedule 8) :
    CheckedModel rules (MACNormalization.condition orders) (family orders) :=
  extendModel (Structural.model orders true)

/-- Reuse an explicitly provided comparison of the expanded old paths. -/
def liftCoherence {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := rules) p q)
    (coherence : MixedCell (expandTrack first) (expandTrack second)) : Cell first second :=
  (eliminateTrack first).cell.trans ((embedCell coherence).trans (eliminateTrack second).cell.symm)

/-- Existence of a comparison is equivalent in the two presentations.
Both constructive directions retain the supplied comparison footprint. -/
theorem comparison_iff {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := rules) p q) :
    Nonempty (Cell first second) ↔ Nonempty (MixedCell (expandTrack first) (expandTrack second)) := by
  constructor
  · rintro ⟨cell⟩
    exact ⟨(projectCell cell).cell⟩
  · rintro ⟨cell⟩
    exact ⟨liftCoherence first second cell⟩

theorem liftCoherence_support {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := rules) p q)
    (coherence : MixedCell (expandTrack first) (expandTrack second)) :
    PresentedCell.support (liftCoherence first second coherence) = PresentedCell.support coherence := by
  have bounds := coherence.boundaries
  simp only [expandTrack_support] at bounds
  simp only [liftCoherence, PresentedCell.support, eliminateTrack_support, embedCell_support]
  ext label
  have one : label ∈ RewriteTrack.support first → label ∈ PresentedCell.support coherence := fun member => bounds.1 member
  have two : label ∈ RewriteTrack.support second → label ∈ PresentedCell.support coherence := fun member => bounds.2 member
  simp only [Finset.mem_union]
  tauto

theorem liftCoherence_fresh {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := rules) p q)
    (coherence : MixedCell (expandTrack first) (expandTrack second)) (changed : Finset Nat) :
    fresh (PresentedCell.support (liftCoherence first second coherence)) changed =
      fresh (PresentedCell.support coherence) changed := by
  rw [liftCoherence_support]

theorem liftCoherence_repaired_joint {old updated : Nat → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (checked : CheckedModel (@Structural.rules true) updated Value) {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := rules) p q)
    (coherence : MixedCell (expandTrack first) (expandTrack second)) (changed : Finset Nat)
    (cached : Holds old (PresentedCell.support coherence))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (PresentedCell.support coherence) changed))
    (law : PMF (Context × Bundle Value a)) :
    ∃ left : Holds updated p.needs, ∃ right : Holds updated q.needs,
      law.bind (fun past => (evaluate checked.base p left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate checked.base q right past.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (liftCoherence first second coherence)) := by
    rw [liftCoherence_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (liftCoherence first second coherence)) changed) := by
    rw [liftCoherence_support]; exact rechecked
  exact (liftCoherence first second coherence).repaired_joint (extendModel checked) changed cached' unchanged rechecked' law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
