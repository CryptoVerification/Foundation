import Foundation.Crypto.Logic.Polygraph.MixedCircuitStateful

/-! Deterministic representation of ONE threaded state commutes with every
mixed circuit when it commutes with each actual box kernel. Port values can
be nontrivial and correlated. Tensor remains ordered; no state copy, effectful
interchange, compiler, or runtime contract is inferred from this theorem. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget OldState NewState : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {condition : Requirement → Prop}
variable {Value : signature.PortAtom → Type}
set_option backward.isDefEq.respectTransparency false

/-- Only the implicit shared state changes representation. -/
def stateMap {n : Port signature} (move : OldState → NewState)
    (pair : OldState × Bundle Value n) : NewState × Bundle Value n := (move pair.1, pair.2)

structure Simulation (old : Model signature condition Value OldState)
    (updated : Model signature condition Value NewState) (move : OldState → NewState) : Prop where
  box : ∀ label (valid : Holds condition (signature.needs label)) state input,
    (old.box label valid state input).map (stateMap move) = updated.box label valid (move state) input

theorem Simulation.evaluate {old : Model signature condition Value OldState}
    {updated : Model signature condition Value NewState} {move : OldState → NewState}
    (simulation : Simulation old updated move) {n m} (circuit : Circuit signature n m)
    (valid : Holds condition circuit.needs) (state : OldState) (input : Bundle Value n) :
    (Stateful.evaluate old circuit valid state input).map (stateMap move) =
      Stateful.evaluate updated circuit valid (move state) input := by
  induction circuit generalizing state with
  | wire wire => simp only [Stateful.evaluate, PMF.pure_map, stateMap]
  | box label => exact simulation.box label valid state input
  | seq first second one two =>
      simp only [Stateful.evaluate, PMF.map_bind]
      simp_rw [two]
      rw [← one (valid.restrict Finset.subset_union_left) state input, PMF.bind_map]
      rfl
  | @tensor n m n' m' first second one two =>
      simp only [Stateful.evaluate, PMF.map_bind, PMF.map_comp, Function.comp_def, stateMap]
      have right (left : OldState × Bundle Value m) :=
        congrArg (PMF.map (fun pair : NewState × Bundle Value m' => (pair.1, (left.2, pair.2))))
          (two (valid.restrict Finset.subset_union_right) left.1 input.2)
      simp only [PMF.map_comp, stateMap, Function.comp_def] at right
      simp_rw [right]
      rw [← one (valid.restrict Finset.subset_union_left) state input.1, PMF.bind_map]
      rfl

/-- Retain the original context, old initial state and old port input. -/
theorem Simulation.joint {old : Model signature condition Value OldState}
    {updated : Model signature condition Value NewState} {move : OldState → NewState}
    (simulation : Simulation old updated move) {Context : Type} {n m}
    (circuit : Circuit signature n m) (valid : Holds condition circuit.needs)
    (law : PMF (Context × (OldState × Bundle Value n))) :
    law.bind (fun past => (Stateful.evaluate old circuit valid past.2.1 past.2.2).map
      (fun result => (past, stateMap move result))) =
    law.bind (fun past => (Stateful.evaluate updated circuit valid (move past.2.1) past.2.2).map
      (fun result => (past, result))) := by
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  have same := congrArg (PMF.map (fun result => (past, result)))
    (simulation.evaluate circuit valid past.2.1 past.2.2)
  simpa only [PMF.map_comp, Function.comp_def] using same

omit [DecidableEq Requirement] in
/-- Analysis of sampled data is equivariant under any representation of the
retained physical frame, because the lifted boxes leave that frame intact. -/
theorem lift_simulation (model : MixedCircuit.Model signature condition Value) (move : OldState → NewState) :
    Simulation (Stateful.lift model) (Stateful.lift model) move := by
  constructor
  intro label valid state input
  simp only [Stateful.lift, PMF.map_comp, Function.comp_def, stateMap]

theorem lift_state_marginal (model : MixedCircuit.Model signature condition Value)
    {n m} (circuit : Circuit signature n m) (valid : Holds condition circuit.needs)
    (state : OldState) (input : Bundle Value n) :
    (Stateful.evaluate (Stateful.lift model) circuit valid state input).map Prod.fst = PMF.pure state := by
  rw [evaluate_lift, PMF.map_comp]
  exact PMF.map_const _ _

end CryptoLogic.Polygraph.MixedCircuit.Stateful
