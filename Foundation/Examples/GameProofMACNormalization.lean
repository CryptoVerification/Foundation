import Foundation.Crypto.Logic.Polygraph.GameProofNormalization
import Foundation.Examples.GameCoherenceMAC

/-! A single adaptive MAC game with any finite chain of preparation-order
changes followed by forgery elimination. One schematic local branching rule
is checked semantically; the global higher diagram is generated, not supplied.
Preparatory coordinate order is not the attacker's query order. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization
open Foundation.Probability
open Foundation.Logic.Polygraph.ScheduleCertificate
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Vertex where | stage (index : Nat) | finish deriving DecidableEq, Repr
inductive Atom where | schedule (index : Nat) | eliminate (index : Nat) deriving DecidableEq, Repr

def layout : Layout Vertex Atom Nat Unit where
  source := fun | .schedule n => .stage (n + 1) | .eliminate n => .stage n
  target := fun | .schedule n => .stage n | .eliminate _ => .finish
  needs := fun | .schedule _ => ∅ | .eliminate n => {n}
  charges := fun | .schedule _ => 0 | .eliminate _ => {()}

def relators (index : Nat) : Relator layout where
  source := .stage (index + 1)
  target := .finish
  left := .seq (.atom (Atom.schedule index)) (.atom (Atom.eliminate index))
  right := .atom (Atom.eliminate (index + 1))
  needs := ∅
  balanced := zero_add _

def strategy : Strategy layout .finish where
  rank := fun | .stage n => n + 1 | .finish => 0
  decreases := by intro label; cases label <;> simp [layout]
  terminal := by intro label; cases label <;> simp [layout]
  next := fun | .finish => .done | .stage 0 => .step (Atom.eliminate 0) | .stage (n + 1) => .step (Atom.schedule n)

def diamonds : {a b c : Vertex} → (first : Transition layout a b) → (second : Transition layout a c) →
    LocalDiamond layout relators first second := by
  intro a b c first second
  rcases first with ⟨one, rfl, rfl⟩
  rcases second with ⟨two, same, rfl⟩
  cases one with
  | schedule n =>
    cases two with
    | schedule m =>
      simp only [layout, Vertex.stage.injEq, Nat.add_left_inj] at same
      cases same
      exact ⟨.stage n, .identity _, .identity _, .refl _⟩
    | eliminate m =>
      simp only [layout, Vertex.stage.injEq] at same
      cases same
      exact ⟨.finish, .atom (Atom.eliminate n), .identity _, .trans (.rule n) (.symm (.rightUnit _))⟩
  | eliminate n =>
    cases two with
    | schedule m =>
      simp only [layout, Vertex.stage.injEq] at same
      cases same
      exact ⟨.finish, .identity _, .atom (Atom.eliminate m), .trans (.rightUnit _) (.symm (.rule m))⟩
    | eliminate m =>
      simp only [layout, Vertex.stage.injEq] at same
      cases same
      exact ⟨.finish, .identity _, .identity _, .refl _⟩

def direct (index : Nat) : Plan layout (.stage index) .finish := .atom (Atom.eliminate index)

def generated (index : Nat) : Cell layout relators (direct index) (strategy.normal (.stage index)) :=
  terminalCoherence strategy diamonds _ _

noncomputable def price (_ : Unit) : ℝ≥0∞ := (256 : ℝ≥0∞)⁻¹

def condition (orders : Nat → Schedule 8) (index : Nat) : Prop :=
  (GameCoherence.Examples.MAC.fullGame (orders index)).probability ≤ (256 : ℝ≥0∞)⁻¹

/-- Only the success flag is changed. Secret state and the complete actual
oracle transcript are retained, rather than collapsing the result to Unit. -/
def sanitize (outcome : GameCoherence.Examples.MAC.FullOutcome) : GameCoherence.Examples.MAC.FullOutcome :=
  {outcome with result := false}

theorem sanitize_state (outcome : GameCoherence.Examples.MAC.FullOutcome) :
    (sanitize outcome).state = outcome.state := rfl

theorem sanitize_trace (outcome : GameCoherence.Examples.MAC.FullOutcome) :
    (sanitize outcome).trace = outcome.trace := rfl

noncomputable def retainedGame (anchor : Schedule 8) : Observed :=
  ⟨GameCoherence.Examples.MAC.FullOutcome,
    .sample ((GameCoherence.Examples.MAC.fullLaw anchor).map sanitize), fun outcome => outcome.result = true⟩

noncomputable def eliminateRetaining (anchor order : Schedule 8)
    (secure : (GameCoherence.Examples.MAC.fullGame order).probability ≤ (256 : ℝ≥0∞)⁻¹) :
    Step (GameCoherence.Examples.MAC.fullGame order) (retainedGame anchor) where
  kernel outcome := PMF.pure (sanitize outcome)
  preserve := by
    change (GameCoherence.Examples.MAC.fullLaw order).map sanitize =
      (GameCoherence.Examples.MAC.fullLaw anchor).map sanitize
    rw [GameCoherence.Examples.MAC.full_law_eq order anchor]
  bad pair := pair.1.result = true
  agree x _ y reachable good := by
    have same := (PMF.mem_support_pure_iff _ _).mp reachable
    subst y
    exact iff_of_false good (by change ¬((false : Bool) = true); decide)
  loss := (256 : ℝ≥0∞)⁻¹
  bound := by
    change eventProb ((GameCoherence.Examples.MAC.fullLaw order).bind fun x =>
      (PMF.pure (sanitize x)).map (fun y => (x, y))) (fun pair => pair.1.result = true) ≤ _
    simp only [PMF.pure_map]
    change eventProb ((GameCoherence.Examples.MAC.fullLaw order).map (fun x => (x, sanitize x))) _ ≤ _
    rw [eventProb_map]
    exact secure

noncomputable def game (orders : Nat → Schedule 8) : Vertex → Observed
  | .stage n => GameCoherence.Examples.MAC.fullGame (orders n)
  | .finish => retainedGame (orders 0)

noncomputable def baseModel (orders : Nat → Schedule 8) : Model layout (condition orders) price where
  game := game orders
  atom label proof := match label with
    | .schedule n => GameCoherence.Examples.MAC.schedulePath (orders (n + 1)) (orders n)
    | .eliminate n => .step (eliminateRetaining (orders 0) (orders n) (proof n (by simp [layout])))
  atom_loss := by
    intro label proof
    cases label <;> simp [layout, totalCharge, price, Path.loss, GameCoherence.Examples.MAC.schedule_loss,
      eliminateRetaining]

noncomputable def model (orders : Nat → Schedule 8) : HigherModel layout relators (condition orders) price where
  base := baseModel orders
  comparison := by
    intro index left right extra
    change Cell4
      (.seq (GameCoherence.Examples.MAC.schedulePath (orders (index + 1)) (orders index))
        (.step (eliminateRetaining (orders 0) (orders index)
          (left index (by simp [relators, Plan.needs, layout])))))
      (.step (eliminateRetaining (orders 0) (orders (index + 1))
        (right (index + 1) (by simp [relators, Plan.needs, layout]))))
    apply Cell4.generator
    constructor
    · intro state
      simp only [Path.kernel, GameCoherence.Examples.MAC.schedule_kernel, eliminateRetaining, PMF.pure_bind]
    · simp only [Path.loss, GameCoherence.Examples.MAC.schedule_loss, eliminateRetaining, zero_add]

theorem conditions (orders : Nat → Schedule 8) (needed : Finset Nat) : Holds (condition orders) needed :=
  fun index _ => GameCoherence.Examples.MAC.full_security (orders index)

noncomputable def realized (orders : Nat → Schedule 8) (index : Nat) :
    Cell4 (evaluate (baseModel orders) (direct index)
      ((conditions orders _).restrict ((generated index).endpoint_needs layout relators).1))
      (evaluate (baseModel orders) (strategy.normal (.stage index))
        ((conditions orders _).restrict ((generated index).endpoint_needs layout relators).2)) :=
  evaluateCell (model orders) (generated index) (conditions orders _)

theorem generated_bound (orders : Nat → Schedule 8) (index : Nat) :
    probabilityGap (game orders (.stage index)).probability (game orders .finish).probability ≤ (256 : ℝ≥0∞)⁻¹ := by
  simpa only [direct, Plan.charges, layout, totalCharge, Multiset.map_singleton, Multiset.sum_singleton, price, baseModel] using
    evaluate_sound (baseModel orders) (direct index) (conditions orders _)

/-- The theorem ranges over every terminal plan in this presentation, rather
than just the displayed direct and strategy routes. -/
theorem terminal_charges {index : Nat} (plan : Plan layout (.stage index) .finish) :
    plan.charges layout = {()} :=
  (terminalCoherence strategy diamonds plan (direct index)).charge_eq layout relators

theorem arbitrary_bound (orders : Nat → Schedule 8) {index : Nat}
    (plan : Plan layout (.stage index) .finish) :
    probabilityGap (game orders (.stage index)).probability (game orders .finish).probability ≤ (256 : ℝ≥0∞)⁻¹ := by
  have bound := evaluate_sound (baseModel orders) plan (conditions orders _)
  rw [terminal_charges plan] at bound
  simpa only [totalCharge, Multiset.map_singleton, Multiset.sum_singleton, price, baseModel] using bound

/-- Semantic comparison for arbitrary terminal proofs is obtained from the
generated diagram and its generated conditions. -/
noncomputable def arbitraryDiagram (orders : Nat → Schedule 8) {index : Nat}
    (first second : Plan layout (.stage index) .finish) :=
  evaluateCell (model orders) (terminalCoherence strategy diamonds first second) (conditions orders _)

/-- Any terminal proof preserves the original secret/oracle state and trace
pointwise; only the result flag is replaced. This is stronger than equal
terminal marginals or equality after erasing the full outcome to Unit. -/
theorem arbitrary_kernel (orders : Nat → Schedule 8) {index : Nat}
    (plan : Plan layout (.stage index) .finish) (proof : Holds (condition orders) (plan.needs layout))
    (outcome : GameCoherence.Examples.MAC.FullOutcome) :
    (evaluate (baseModel orders) plan proof).kernel outcome = PMF.pure (sanitize outcome) :=
  (arbitraryDiagram orders plan (direct index)).sound.kernel_eq outcome

theorem arbitrary_state (orders : Nat → Schedule 8) {index : Nat}
    (plan : Plan layout (.stage index) .finish) (proof : Holds (condition orders) (plan.needs layout))
    (outcome : GameCoherence.Examples.MAC.FullOutcome) :
    ((evaluate (baseModel orders) plan proof).kernel outcome).map (·.state) = PMF.pure outcome.state := by
  rw [arbitrary_kernel]
  exact PMF.pure_map _ _

theorem arbitrary_trace (orders : Nat → Schedule 8) {index : Nat}
    (plan : Plan layout (.stage index) .finish) (proof : Holds (condition orders) (plan.needs layout))
    (outcome : GameCoherence.Examples.MAC.FullOutcome) :
    ((evaluate (baseModel orders) plan proof).kernel outcome).map (·.trace) = PMF.pure outcome.trace := by
  rw [arbitrary_kernel]
  exact PMF.pure_map _ _

theorem generated_joint (orders : Nat → Schedule 8) (index : Nat) :
    (evaluate (baseModel orders) (direct index)
      ((conditions orders _).restrict ((generated index).endpoint_needs layout relators).1)).joint =
    (evaluate (baseModel orders) (strategy.normal (.stage index))
      ((conditions orders _).restrict ((generated index).endpoint_needs layout relators).2)).joint :=
  (realized orders index).joint_eq

theorem repairedConditions (old updated : Nat → Schedule 8) (index : Nat) (changed : Finset Nat)
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (condition updated) ((generated index).fresh layout relators changed)) :
    Holds (condition updated) ((generated index).needs layout relators) := by
  apply repair (conditions old _) _ rechecked
  intro label outside cached
  simpa only [condition, ← unchanged label outside] using cached

/-- Repair uses the generated whole diagram's conditions, including the
intermediate orders. It is not restricted to the two boundary plans. -/
noncomputable def repairedDiagram (old updated : Nat → Schedule 8) (index : Nat) (changed : Finset Nat)
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (condition updated) ((generated index).fresh layout relators changed)) :=
  evaluateCell (model updated) (generated index) (repairedConditions old updated index changed unchanged rechecked)

/-- info: (4, 1, false, 1, 1, true, true) -/
#guard_msgs in
#eval (((generated 3).needs layout relators).card, ((generated 3).fresh layout relators {1}).card,
  (generated 3).checkReuse layout relators {1}, ((direct 3).charges layout).card,
  ((strategy.normal (.stage 3)).charges layout).card,
  decide (1 ∉ (direct 3).needs layout ∪ (strategy.normal (.stage 3)).needs layout),
  decide (1 ∈ (generated 3).needs layout relators))

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization
