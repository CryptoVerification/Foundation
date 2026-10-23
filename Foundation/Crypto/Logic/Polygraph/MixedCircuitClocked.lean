import Foundation.Crypto.Logic.Polygraph.MixedCircuitStateful
import Foundation.Crypto.Semantics.TimedExecution

/-! The original mixed syntax can schedule chunks of ONE continuing transition
system. Wires act on port data only. Both children of tensor use the same step
function, code and evolving state; this is not arbitrary concurrent execution
or a compiler for switching between native programs. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.Clocked
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Logic.Polygraph.StructuralTransport
set_option backward.isDefEq.respectTransparency false
variable {State : Type}

def signature : Signature Nat Unit Unit where
  PortAtom := Unit
  inputs _ := .unit
  outputs _ := .unit
  needs _ := ∅
  charges _ := 0

abbrev Values (_ : Unit) := PUnit

def ticks : {n m : Port signature} → Circuit signature n m → Nat
  | _, _, .wire _ => 0
  | _, _, .box duration => duration
  | _, _, .seq first second => ticks first + ticks second
  | _, _, .tensor first second => ticks first + ticks second

def output : {n m : Port signature} → Circuit signature n m → Bundle Values n → Bundle Values m
  | _, _, .wire wire, input => wire.eval Values input
  | _, _, .box _, _ => PUnit.unit
  | _, _, .seq first second, input => output second (output first input)
  | _, _, .tensor first second, input => (output first input.1, output second input.2)

noncomputable def model (step : State → PMF State) : Model signature (fun _ => True) Values State where
  box duration _ state _ := (TimedExecution.eval step duration state).map fun final => (final, PUnit.unit)

theorem needs_empty {n m} (circuit : Circuit signature n m) : circuit.needs = ∅ := by
  induction circuit with
  | wire => rfl
  | box => rfl
  | seq first second one two => simp only [Circuit.needs, one, two, Finset.union_self]
  | tensor first second one two => simp only [Circuit.needs, one, two, Finset.union_self]

theorem valid {n m} (circuit : Circuit signature n m) : Holds (fun _ => True) circuit.needs := fun _ _ => True.intro

/-- Exact equality with the original unbroken stochastic execution. -/
theorem evaluate_exact (step : State → PMF State) {n m} (circuit : Circuit signature n m)
    (proof : Holds (fun _ => True) circuit.needs) (state : State) (input : Bundle Values n) :
    evaluate (model step) circuit proof state input =
      (TimedExecution.eval step (ticks circuit) state).map (fun final => (final, output circuit input)) := by
  induction circuit generalizing state with
  | wire wire => simp only [evaluate, ticks, TimedExecution.eval, PMF.pure_map, output]
  | box duration => rfl
  | seq first second one two =>
      simp only [evaluate, ticks, output, one, PMF.bind_map, Function.comp_def, two,
        TimedExecution.eval_add, PMF.map_bind]
  | tensor first second one two =>
      simp only [evaluate, ticks, output, one, PMF.bind_map, Function.comp_def, two,
        PMF.map_comp, TimedExecution.eval_add, PMF.map_bind]

theorem state_marginal (step : State → PMF State) {n m} (circuit : Circuit signature n m)
    (proof : Holds (fun _ => True) circuit.needs) (state : State) (input : Bundle Values n) :
    (evaluate (model step) circuit proof state input).map Prod.fst =
      TimedExecution.eval step (ticks circuit) state := by
  rw [evaluate_exact, PMF.map_comp]
  exact PMF.map_id _

theorem same_ticks (step : State → PMF State) {n m n' m'}
    (first : Circuit signature n m) (second : Circuit signature n' m')
    (one : Holds (fun _ => True) first.needs) (two : Holds (fun _ => True) second.needs)
    (duration : ticks first = ticks second) (state : State) (input : Bundle Values n) (input' : Bundle Values n') :
    (evaluate (model step) first one state input).map Prod.fst =
      (evaluate (model step) second two state input').map Prod.fst := by
  rw [state_marginal, state_marginal, duration]

/-- Keep the full correlated initial context and state, not just a marginal. -/
theorem exact_joint {Context : Type} (step : State → PMF State) {n m}
    (circuit : Circuit signature n m) (proof : Holds (fun _ => True) circuit.needs)
    (law : PMF (Context × (State × Bundle Values n))) :
    law.bind (fun past => (evaluate (model step) circuit proof past.2.1 past.2.2).map (fun result => (past, result.1))) =
      law.bind (fun past => (TimedExecution.eval step (ticks circuit) past.2.1).map (fun final => (past, final))) := by
  congr 1
  funext past
  rw [evaluate_exact, PMF.map_comp]
  rfl

end CryptoLogic.Polygraph.MixedCircuit.Stateful.Clocked
