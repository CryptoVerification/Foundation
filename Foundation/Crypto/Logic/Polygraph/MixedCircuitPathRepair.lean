import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedHigher

/-! Scope boundary for higher repair claims. Endpoint kernel repair already
follows from one rewrite track, without a higher basis or a comparison cell.
The support of that track can be smaller than the comparison's support.
These results do not compare proof-derived reductions or execution resources. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

namespace RewriteTrack

theorem repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators updated Value) {n m} {a b : Circuit signature n m}
    (path : RewriteTrack (relators := relators) a b) (changed : Finset Requirement)
    (cached : Holds old (support path))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (support path) changed)) :
    ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
      ∀ input, evaluate model.base a left input = evaluate model.base b right input := by
  let valid := CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.repair cached unchanged rechecked
  exact ⟨valid.restrict path.boundaries.1, valid.restrict path.boundaries.2,
    fun input => path.sound model valid _ _ input⟩

theorem repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    {Context : Type} (model : CheckedModel relators updated Value) {n m}
    {a b : Circuit signature n m} (path : RewriteTrack (relators := relators) a b)
    (changed : Finset Requirement) (cached : Holds old (support path))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (support path) changed))
    (law : PMF (Context × Bundle Value n)) :
    ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
      law.bind (fun past => (evaluate model.base a left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base b right past.2).map (fun next => (past, next))) := by
  obtain ⟨left, right, equal⟩ := path.repaired model changed cached unchanged rechecked
  refine ⟨left, right, ?_⟩
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  rw [equal past.2]

end RewriteTrack

namespace PresentedCell

/-- The left track's declared recheck set is included in the higher cell's.
This is sufficiency of a smaller set for endpoint equality, not minimality. -/
theorem left_recheck_subset {basis : HigherBasis relators} {n m}
    {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) (changed : Finset Requirement) :
    fresh (RewriteTrack.support p) changed ⊆ fresh (support cell) changed := by
  intro label member
  exact Finset.mem_inter.mpr ⟨cell.boundaries.1 (Finset.mem_inter.mp member).1,
    (Finset.mem_inter.mp member).2⟩

end PresentedCell
end CryptoLogic.Polygraph.MixedCircuit
