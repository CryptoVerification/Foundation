import Foundation.Crypto.Logic.Polygraph.GameProofHigher
import Foundation.Examples.GameCoherence

/-! A higher diagram can depend on a comparison condition absent from both
outer plans. After an identity map changes to a fair-bit flip, endpoint laws
still agree but the interior conditional-kernel comparison is impossible. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.Interior
open Foundation.Probability
open scoped ENNReal

def layout : Layout Unit Unit Unit Unit where
  source _ := ()
  target _ := ()
  needs _ := ∅
  charges _ := 0

def identityPlan : Plan layout () () := .identity ()
def mapPlan : Plan layout () () := .atom ()

def relators (_ : Unit) : Relator layout where
  source := ()
  target := ()
  left := identityPlan
  right := mapPlan
  needs := {()}
  balanced := rfl

def roundTrip : Cell layout relators identityPlan identityPlan :=
  .trans (.rule ()) (.symm (.rule ()))

def alternative : Cell layout relators identityPlan identityPlan := .refl identityPlan

def condition (flip : Bool) (_ : Unit) : Prop := flip = false

theorem endpoints_need_nothing : identityPlan.needs layout = ∅ := rfl

theorem interior_condition : roundTrip.needs layout relators = {()} := by decide

theorem old_conditions : Holds (condition false) (roundTrip.needs layout relators) := fun _ _ => rfl

theorem missing_new_condition : ¬ Holds (condition true) (roundTrip.needs layout relators) := by
  intro proof
  have impossible := proof () (by decide)
  cases impossible

theorem endpoint_check_accepts : checkReuse (identityPlan.needs layout) {()} = true := by decide

theorem diagram_check_rejects : roundTrip.checkReuse layout relators {()} = false := by decide

theorem alternative_check_accepts : alternative.checkReuse layout relators {()} = true := by decide

noncomputable def baseModel (flip : Bool) : Model layout (condition flip) (fun _ => (0 : ℝ≥0∞)) where
  game _ := GameCoherence.Examples.fairState
  atom _ _ := if flip then .step GameCoherence.Examples.flipBit else .identity GameCoherence.Examples.fairState
  atom_loss := by intro label proof; cases flip <;> rfl

noncomputable def model (flip : Bool) : HigherModel layout relators (condition flip) (fun _ => (0 : ℝ≥0∞)) where
  base := baseModel flip
  comparison := by
    intro label left right proof
    have same := proof () (by simp [relators])
    subst flip
    exact .refl _

/-- The rejection corresponds to an actually invalid interior local rule,
not merely a changed annotation or unequal endpoint marginal. -/
theorem new_local_rule_impossible : ¬ Nonempty
    (Cell4 (evaluate (baseModel true) identityPlan (fun _ member => False.elim (Finset.notMem_empty _ member)))
      (evaluate (baseModel true) mapPlan (fun _ member => False.elim (Finset.notMem_empty _ member)))) := by
  simpa only [evaluate, baseModel, identityPlan, mapPlan, Bool.true_eq, ↓reduceIte] using
    GameCoherence.Examples.no_identity_flip_comparison

/-- info: (0, 1, 1, true, false, true) -/
#guard_msgs in
#eval ((identityPlan.needs layout).card, (roundTrip.needs layout relators).card,
  (roundTrip.fresh layout relators {()}).card, checkReuse (identityPlan.needs layout) {()},
  roundTrip.checkReuse layout relators {()}, alternative.checkReuse layout relators {()})

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.Interior
