import Foundation.Crypto.Logic.Polygraph.GameProofHigher
import Foundation.Examples.GameCoherenceMAC

/-! Named verification conditions for two routes of an existing adaptive MAC
proof: reschedule then eliminate forgery, or eliminate directly. Both keep
the same source game, have error 1/256, and use the retained conditional-kernel
semantics. Editing the intermediate schedule rechecks one declared condition. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACRepair
open Foundation.Probability
open Foundation.Logic.Polygraph.ScheduleCertificate
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Vertex where | start | middle | finish deriving DecidableEq, Repr
inductive Atom where | schedule | last | first deriving DecidableEq, Repr

def layout : Layout Vertex Atom Bool Unit where
  source := fun | .schedule => .start | .last => .middle | .first => .start
  target := fun | .schedule => .middle | .last => .finish | .first => .finish
  needs := fun | .schedule => ∅ | .last => {true} | .first => {false}
  charges := fun | .schedule => 0 | .last | .first => {()}

def scheduledPlan : Plan layout .start .finish := .seq (.atom Atom.schedule) (.atom Atom.last)
def directPlan : Plan layout .start .finish := .atom Atom.first

def relators (_ : Unit) : Relator layout where
  source := .start
  target := .finish
  left := scheduledPlan
  right := directPlan
  needs := ∅
  balanced := by simp [scheduledPlan, directPlan, Plan.charges, layout]

def diagram : Cell layout relators scheduledPlan directPlan := .rule ()

theorem generated_needs : diagram.needs layout relators = {false, true} := by decide

theorem generated_fresh : diagram.fresh layout relators {true} = {true} := by decide

noncomputable def price (_ : Unit) : ℝ≥0∞ := (256 : ℝ≥0∞)⁻¹

def condition (parameter : Schedule 8 × Schedule 8) (which : Bool) : Prop :=
  (GameCoherence.Examples.MAC.fullGame (if which then parameter.2 else parameter.1)).probability ≤ (256 : ℝ≥0∞)⁻¹

/-- The security inequality is supplied as the named local condition. -/
noncomputable def eliminateGiven (schedule : Schedule 8)
    (secure : (GameCoherence.Examples.MAC.fullGame schedule).probability ≤ (256 : ℝ≥0∞)⁻¹) :
    Step (GameCoherence.Examples.MAC.fullGame schedule) GameCoherence.Examples.MAC.noForgery where
  kernel _ := PMF.pure ()
  preserve := PMF.bind_const _ _
  bad pair := pair.1.result = true
  agree _ _ _ _ good := iff_of_false good id
  loss := (256 : ℝ≥0∞)⁻¹
  bound := by
    change eventProb ((GameCoherence.Examples.MAC.fullLaw schedule).bind fun x =>
      (PMF.pure ()).map (fun y => (x, y))) (fun pair => pair.1.result = true) ≤ _
    simp only [PMF.pure_map]
    change eventProb ((GameCoherence.Examples.MAC.fullLaw schedule).map (fun x => (x, ()))) _ ≤ _
    rw [eventProb_map]
    exact secure

noncomputable def game (parameter : Schedule 8 × Schedule 8) : Vertex → Observed
  | .start => GameCoherence.Examples.MAC.fullGame parameter.1
  | .middle => GameCoherence.Examples.MAC.fullGame parameter.2
  | .finish => GameCoherence.Examples.MAC.noForgery

noncomputable def baseModel (parameter : Schedule 8 × Schedule 8) : Model layout (condition parameter) price where
  game := game parameter
  atom label proof := match label with
    | .schedule => GameCoherence.Examples.MAC.schedulePath parameter.1 parameter.2
    | .last => .step (eliminateGiven parameter.2 (proof true (by simp [layout])))
    | .first => .step (eliminateGiven parameter.1 (proof false (by simp [layout])))
  atom_loss := by
    intro label proof
    cases label <;> simp [layout, totalCharge, price, Path.loss, GameCoherence.Examples.MAC.schedule_loss, eliminateGiven]

noncomputable def model (parameter : Schedule 8 × Schedule 8) : HigherModel layout relators (condition parameter) price where
  base := baseModel parameter
  comparison := by
    intro label left right extra
    cases label
    change Cell4
      (.seq (GameCoherence.Examples.MAC.schedulePath parameter.1 parameter.2)
        (.step (eliminateGiven parameter.2 (left true (by simp [relators, scheduledPlan, Plan.needs, layout])))))
      (.step (eliminateGiven parameter.1 (right false (by simp [relators, directPlan, Plan.needs, layout]))))
    apply Cell4.generator
    constructor
    · intro state
      simp only [Path.kernel, GameCoherence.Examples.MAC.schedule_kernel, eliminateGiven, PMF.pure_bind]
    · simp only [Path.loss, GameCoherence.Examples.MAC.schedule_loss, eliminateGiven, zero_add]

theorem cached_conditions (first last : Schedule 8) : Holds (condition (first, last)) (diagram.needs layout relators) := by
  intro which _
  cases which
  · exact GameCoherence.Examples.MAC.full_security first
  · exact GameCoherence.Examples.MAC.full_security last

theorem unchanged_condition (first oldLast newLast : Schedule 8) :
    ∀ which ∉ ({true} : Finset Bool), condition (first, oldLast) which → condition (first, newLast) which := by
  intro which outside proof
  cases which
  · exact proof
  · simp at outside

theorem rechecked_condition (first newLast : Schedule 8) :
    Holds (condition (first, newLast)) (diagram.fresh layout relators {true}) := by
  intro which member
  rw [generated_fresh, Finset.mem_singleton] at member
  subst which
  exact GameCoherence.Examples.MAC.full_security newLast

theorem repairedConditions (first oldLast newLast : Schedule 8) :
    Holds (condition (first, newLast)) (diagram.needs layout relators) :=
  repair (cached_conditions first oldLast) (unchanged_condition first oldLast newLast) (rechecked_condition first newLast)

noncomputable def scheduledRealization (first oldLast newLast : Schedule 8) :
    Path (GameCoherence.Examples.MAC.fullGame first) GameCoherence.Examples.MAC.noForgery :=
  evaluate (baseModel (first, newLast)) scheduledPlan
    ((repairedConditions first oldLast newLast).restrict (diagram.endpoint_needs layout relators).1)

noncomputable def directRealization (first oldLast newLast : Schedule 8) :
    Path (GameCoherence.Examples.MAC.fullGame first) GameCoherence.Examples.MAC.noForgery :=
  evaluate (baseModel (first, newLast)) directPlan
    ((repairedConditions first oldLast newLast).restrict (diagram.endpoint_needs layout relators).2)

noncomputable def repairedDiagram (first oldLast newLast : Schedule 8) :
    Cell4 (scheduledRealization first oldLast newLast) (directRealization first oldLast newLast) :=
  evaluateCell (model (first, newLast)) diagram (repairedConditions first oldLast newLast)

theorem repaired_loss (first oldLast newLast : Schedule 8) :
    (scheduledRealization first oldLast newLast).loss = (256 : ℝ≥0∞)⁻¹ := by
  simpa only [scheduledRealization, scheduledPlan, Plan.charges, layout, totalCharge, Multiset.zero_add,
    Multiset.map_singleton, Multiset.sum_singleton, price] using
    evaluate_loss (baseModel (first, newLast)) scheduledPlan
      ((repairedConditions first oldLast newLast).restrict (diagram.endpoint_needs layout relators).1)

theorem repaired_probability_bound (first oldLast newLast : Schedule 8) :
    probabilityGap (GameCoherence.Examples.MAC.fullGame first).probability
      GameCoherence.Examples.MAC.noForgery.probability ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [← repaired_loss first oldLast newLast]
  exact (scheduledRealization first oldLast newLast).sound

/-- Equality of the joint law also retains the original full source outcome,
including the actual oracle state and trace, paired with the final Unit. -/
theorem repaired_joint (first oldLast newLast : Schedule 8) :
    (scheduledRealization first oldLast newLast).joint = (directRealization first oldLast newLast).joint :=
  (repairedDiagram first oldLast newLast).joint_eq

/-- info: (2, 1, false, 1) -/
#guard_msgs in
#eval ((diagram.needs layout relators).card, (diagram.fresh layout relators {true}).card,
  diagram.checkReuse layout relators {true}, (scheduledPlan.charges layout).card)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACRepair
