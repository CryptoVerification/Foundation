import Foundation.Crypto.Logic.Polygraph.GameProofHigher
import Foundation.Examples.GameCoherence

/-! A multiset charge cannot be replaced by a set of charged assumption IDs.
Even an identity conditional kernel need not have zero accumulated proof loss;
a tighter proof and a loss-preserving higher comparison are different. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.BudgetBoundary
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def layout : Layout Unit Unit Unit Unit where
  source _ := ()
  target _ := ()
  needs _ := ∅
  charges _ := {()}

def doubled : Plan layout () () := .seq (.atom ()) (.atom ())
def empty : Plan layout () () := .identity ()

theorem double_charge : (doubled.charges layout).card = 2 := by decide

/-- This holds for every catalog whose local rules preserve symbolic charges. -/
theorem no_charge_preserving_contraction {RelatorId : Type} (relators : RelatorId → Relator layout) :
    ¬ Nonempty (Cell layout relators doubled empty) := by
  rintro ⟨cell⟩
  have impossible := congrArg Multiset.card (cell.charge_eq layout relators)
  change (2 : Nat) = 0 at impossible
  cases impossible

/-- Inflate the valid zero-loss fair-bit flip to the valid but deliberately
loose upper bound 1/2. This does not change its conditional state kernel. -/
noncomputable def chargedFlip : Step GameCoherence.Examples.fairState GameCoherence.Examples.fairState :=
  { GameCoherence.Examples.flipBit with
    loss := 1 / 2
    bound := GameCoherence.Examples.flipBit.bound.trans (show (0 : ℝ≥0∞) ≤ 1 / 2 from bot_le) }

noncomputable def loop : Path GameCoherence.Examples.fairState GameCoherence.Examples.fairState :=
  .seq (.step chargedFlip) (.step chargedFlip)

theorem loop_kernel (state : Bool) : loop.kernel state = PMF.pure state := by
  change (PMF.pure (!state)).bind (fun x => PMF.pure (!x)) = PMF.pure state
  rw [PMF.pure_bind, Bool.not_not]

theorem loop_loss : loop.loss = 1 := by
  change (1 / 2 : ℝ≥0∞) + 1 / 2 = 1
  simpa only [one_div] using ENNReal.inv_two_add_inv_two

theorem no_loss_preserving_contraction : ¬ Nonempty (Cell4 loop (.identity GameCoherence.Examples.fairState)) := by
  rintro ⟨cell⟩
  have impossible := cell.sound.loss_eq
  rw [loop_loss] at impossible
  change (1 : ℝ≥0∞) = 0 at impossible
  norm_num at impossible

noncomputable def model : Model layout (fun _ => True) (fun _ => (1 / 2 : ℝ≥0∞)) where
  game _ := GameCoherence.Examples.fairState
  atom _ _ := .step chargedFlip
  atom_loss := by
    intro label proof
    simp only [Path.loss, chargedFlip, layout, totalCharge, Multiset.map_singleton, Multiset.sum_singleton]

theorem doubled_realization (proof : Holds (fun _ : Unit => True) (doubled.needs layout)) :
    evaluate model doubled proof = loop := rfl

/-- info: (2, 0, 0) -/
#guard_msgs in
#eval ((doubled.charges layout).card, (empty.charges layout).card, (doubled.needs layout).card)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.BudgetBoundary
