import Foundation.Crypto.Logic.Polygraph.MixedCircuitClocked

/-! One schematic local rule fuses two adjacent execution chunks of the SAME
continuing transition system. Its concrete checked model works in every mixed
placement, including tensor. No arbitrary schedule comparison is a root and
no complete higher critical basis is claimed. Symbolic charges are zero;
actual transition budgets are handled by the independently proved evaluator. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.Clocked.Fusion
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def relator (durations : Nat × Nat) : Relator signature where
  inputs := .unit
  outputs := .unit
  left := .seq (.box durations.1) (.box durations.2)
  right := .box (durations.1 + durations.2)
  extra := ∅
  balanced := rfl

noncomputable def checked {State : Type} (step : State → PMF State) :
    CheckedModel relator (fun _ => True) Values State where
  base := model step
  localSound durations valid state input := by
    rw [evaluate_exact, evaluate_exact]
    rfl

/-- A local fusion in any old mixed placement preserves the entire state. -/
theorem sound_in_context {State : Type} (step : State → PMF State) {n m}
    {first second : Circuit signature n m} (change : Step relator first second)
    (state : State) (input : Bundle Values n) :
    evaluate (model step) first (valid first) state input =
      evaluate (model step) second (valid second) state input :=
  Stateful.sound (checked step) change (fun _ _ => True.intro) _ _ state input

/-- Keep the input law, its original state and correlated past in the result. -/
theorem sound_joint {State Context : Type} (step : State → PMF State) {n m}
    {first second : Circuit signature n m} (change : Step relator first second)
    (law : PMF (Context × (State × Bundle Values n))) :
    law.bind (fun past => (evaluate (model step) first (valid first) past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate (model step) second (valid second) past.2.1 past.2.2).map (fun next => (past, next))) :=
  Stateful.sound_joint (checked step) change (fun _ _ => True.intro) _ _ law

end CryptoLogic.Polygraph.MixedCircuit.Stateful.Clocked.Fusion
