import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulHigher
import Foundation.Examples.MixedCircuitFusionCompletion

/-! Every existing MAC/association/wire/fusion/completion rule has a one-state
interpretation provided the original MAC root has a universal stateful proof.
Completion adds no whole-path semantic assumption: its old expansion is used.
The concrete old MAC lift is analysis-only on the extra state; arbitrary native
execution is not silently assigned to the proof-transformation boxes. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulStructural
open Foundation.Probability
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false
variable {State : Type} {condition : Nat → Prop} {Value : signature.PortAtom → Type}

noncomputable def uncompleted (checked : Stateful.CheckedModel MAC.relators condition Value State) :
    Stateful.CheckedModel (@Structural.rules false) condition Value State where
  base := checked.base
  localSound := by
    intro label valid state input
    cases label with
    | crypto stage => exact checked.localSound stage valid state input
    | assoc p q r => simp only [Structural.rules, Stateful.evaluate, PMF.bind_bind]
    | wire change => exact congrArg (fun value => PMF.pure (state, value)) (change.sound Value input)
    | fuseSeq p q =>
        simp only [Structural.rules, Stateful.evaluate, PMF.pure_bind]
        rfl
    | fuseTensor p q =>
        simp only [Structural.rules, Stateful.evaluate, PMF.pure_bind, PMF.pure_map]
        rfl
    | suffix enabled stage tail => cases enabled

noncomputable def completed (checked : Stateful.CheckedModel (@Structural.rules false) condition Value State) :
    Stateful.CheckedModel (@Structural.rules true) condition Value State where
  base := checked.base
  localSound := by
    intro label valid state input
    let change := Primitive.rule (relators := @Structural.rules true) label
    have expanded : Holds condition (RewriteTrack.support (Structural.expandPrimitive change)) := by
      rw [Structural.expandPrimitive_support]
      exact valid
    exact Stateful.track_sound checked (Structural.expandPrimitive change) expanded _ _ state input

noncomputable def fused (checked : Stateful.CheckedModel (@Structural.rules true) condition Value State) :
    Stateful.CheckedModel Structural.Fusion.rules condition Value State where
  base := checked.base
  localSound := by
    intro label valid state input
    let change := Primitive.rule (relators := Structural.Fusion.rules) label
    have expanded : Holds condition (RewriteTrack.support (Structural.Fusion.expandPrimitive change)) := by
      rw [Structural.Fusion.expandPrimitive_support]
      exact valid
    exact Stateful.track_sound checked (Structural.Fusion.expandPrimitive change) expanded _ _ state input

noncomputable def allRules (checked : Stateful.CheckedModel MAC.relators condition Value State) :=
  fused (completed (uncompleted checked))

theorem base_unchanged (checked : Stateful.CheckedModel MAC.relators condition Value State) :
    (allRules checked).base = checked.base := rfl

/-- A concrete interpretation of the original conditional MAC analysis.
The extra state is retained, and is not executed again by proof edits. -/
noncomputable def original (orders : Nat → Schedule 8) :
    Stateful.CheckedModel Structural.Fusion.rules (MACNormalization.condition orders) (family orders) State :=
  allRules (Stateful.liftChecked (MAC.model orders))

/-- Existing explicit local mixed diagrams keep their exact support and can
be interpreted with arbitrary correlated shared state. -/
theorem critical_repaired_joint {old updated : Nat → Prop} {Context : Type}
    (checked : Stateful.CheckedModel (@Structural.rules false) updated Value State)
    (stage : Nat) {target} (tail : Circuit signature finish target) (changed : Finset Nat)
    (cached : Holds old ({stage, stage + 1} ∪ tail.needs))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh ({stage, stage + 1} ∪ tail.needs) changed))
    (law : PMF (Context × (State × Bundle Value (source (stage + 1))))) :
    ∃ left : Holds updated (Circuit.seq (before stage) tail).needs,
    ∃ right : Holds updated (Circuit.seq (after stage) tail).needs,
      law.bind (fun past => (Stateful.evaluate checked.base (.seq (before stage) tail) left past.2.1 past.2.2).map
        (fun next => (past, next))) =
      law.bind (fun past => (Stateful.evaluate checked.base (.seq (after stage) tail) right past.2.1 past.2.2).map
        (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (Structural.criticalCell stage tail)) := by
    rw [Structural.criticalCell_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (Structural.criticalCell stage tail)) changed) := by
    rw [Structural.criticalCell_support]; exact rechecked
  exact Stateful.cell_repaired_joint (completed checked) (Structural.criticalCell stage tail)
    changed cached' unchanged rechecked' law

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulStructural
