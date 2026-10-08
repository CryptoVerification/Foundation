import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureCompletion

/-! Typed mathematical models of finite native procedures. The output type
may retain private randomness needed to describe the complete physical exit;
only the encoded public observation is exposed to an observer. -/
namespace Machine
open Foundation.Probability
universe u v w x
set_option backward.isDefEq.respectTransparency false

structure ProcedureModel (Input : Type u) (Output : Type v) where
  procedure : Procedure Input Output
  ideal : Input → PMF Output
  implements : ∀ input, procedure.execution.semantics input = ideal input
  encode : Input → Output → List Bool
  halt : ∀ input output, output ∈ (ideal input).support →
    (procedure.execution.exit input output).halted = true
  output : ∀ input output, output ∈ (ideal input).support →
    (procedure.execution.exit input output).outputBits = encode input output

namespace ProcedureModel
variable {Input : Type u} {Output : Type v}

/-- Produce the machine-independent stopping contract used by logical
registration. Reindexing fixes the input; it does not prepare any tape. -/
noncomputable def completion (M : ProcedureModel Input Output) (input : Input) :
    TimedExecution.Completion (stepPMF M.procedure.code) (M.procedure.execution.entry input)
      (fun c => c.halted = true) :=
  TimedExecution.Completion.ofProcedure
    (M.procedure.execution.reindex (fun _ : Unit => input)) rfl
    (fun output h => M.halt input output (by
      change output ∈ (M.procedure.execution.semantics input).support at h
      rwa [M.implements] at h))

theorem completion_budget (M : ProcedureModel Input Output) (input : Input) :
    (M.completion input).execution.budget () = M.procedure.execution.budget input := rfl

theorem completion_semantics (M : ProcedureModel Input Output) (input : Input) :
    (M.completion input).execution.semantics () =
      (M.ideal input).map (M.procedure.execution.exit input) := by
  change (M.procedure.execution.semantics input).map _ = _
  rw [M.implements]
  rfl

/-- Keep the original joint distribution of final state and actual cost.
In particular, the model's public marginal does not justify discarding
correlations between a generated key, the physical exit and its duration. -/
theorem completion_costed (M : ProcedureModel Input Output) (input : Input) :
    (M.completion input).execution.costed () =
      (M.procedure.execution.costed input).map
        (fun result => (M.procedure.execution.exit input result.1, result.2)) := rfl

/-- Observe actual native configurations, including failure to halt. -/
noncomputable def execution (M : ProcedureModel Input Output) (input : Input) (horizon : Nat) :
    PMF (Option (List Bool)) :=
  (evalConfigWithin M.procedure.code (M.procedure.execution.entry input) horizon).map
    (fun c => if c.halted then some c.outputBits else none)

/-- The whole physical execution implies the public distribution, at every
horizon above the certified budget. Encoding is an observation, not an
additional machine operation or a claim about encoding CPU cost. -/
theorem execution_eq (M : ProcedureModel Input Output) (input : Input) (horizon : Nat)
    (hBudget : M.procedure.execution.budget input ≤ horizon) :
    M.execution input horizon = (M.ideal input).map (fun output => some (M.encode input output)) := by
  rw [execution, M.procedure.final_run input
    (fun output h => M.halt input output (by rwa [M.implements] at h)) horizon hBudget,
    M.implements, PMF.map_comp]
  simp only [PMF.map]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext output h
  simp [Function.comp_def, M.halt input output h, M.output input output h]

/-- Arbitrary probabilistic observers see exactly the modeled public bytes.
No independence of the hidden result and its execution cost is required. -/
theorem observer_eq (M : ProcedureModel Input Output) (input : Input) (horizon : Nat)
    (hBudget : M.procedure.execution.budget input ≤ horizon)
    (observer : Option (List Bool) → PMF Bool) :
    (M.execution input horizon).bind observer =
      ((M.ideal input).map (fun output => some (M.encode input output))).bind observer := by
  rw [M.execution_eq input horizon hBudget]

/-- Implementations with different input and hidden-result types can still
be substituted when their public model distributions coincide. Both
physical entry conditions and both actual time bounds must be supplied. -/
theorem executions_eq {OtherInput : Type w} {OtherOutput : Type x}
    (M : ProcedureModel Input Output) (N : ProcedureModel OtherInput OtherOutput)
    (input : Input) (other : OtherInput) (time otherTime : Nat)
    (hTime : M.procedure.execution.budget input ≤ time)
    (hOtherTime : N.procedure.execution.budget other ≤ otherTime)
    (hIdeal : (M.ideal input).map (M.encode input) = (N.ideal other).map (N.encode other)) :
    M.execution input time = N.execution other otherTime := by
  rw [M.execution_eq input time hTime, N.execution_eq other otherTime hOtherTime]
  have h := congrArg (fun p : PMF (List Bool) => p.map some) hIdeal
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Transfer quantitative distinguishing advantage, rather than only
perfect equality. Observer running time is a separate certificate. -/
theorem advantage_eq (M : ProcedureModel Input Output) (left right : Input)
    (leftTime rightTime : Nat)
    (hLeft : M.procedure.execution.budget left ≤ leftTime)
    (hRight : M.procedure.execution.budget right ≤ rightTime)
    (observer : Option (List Bool) → PMF Bool) :
    probabilityGap (eventProb ((M.execution left leftTime).bind observer) (· = true))
      (eventProb ((M.execution right rightTime).bind observer) (· = true)) =
    probabilityGap
      (eventProb (((M.ideal left).map (fun output => some (M.encode left output))).bind observer) (· = true))
      (eventProb (((M.ideal right).map (fun output => some (M.encode right output))).bind observer) (· = true)) := by
  rw [M.observer_eq left leftTime hLeft observer, M.observer_eq right rightTime hRight observer]

/-- Equality of modeled public distributions transfers to real executions.
The two inputs may have different certified budgets and chosen horizons. -/
theorem indistinguishable (M : ProcedureModel Input Output) (left right : Input)
    (leftTime rightTime : Nat)
    (hLeft : M.procedure.execution.budget left ≤ leftTime)
    (hRight : M.procedure.execution.budget right ≤ rightTime)
    (hIdeal : (M.ideal left).map (M.encode left) = (M.ideal right).map (M.encode right))
    (observer : Option (List Bool) → PMF Bool) :
    (M.execution left leftTime).bind observer = (M.execution right rightTime).bind observer := by
  rw [M.execution_eq left leftTime hLeft, M.execution_eq right rightTime hRight]
  have h := congrArg (fun p : PMF (List Bool) => p.map some) hIdeal
  simp only [PMF.map_comp, Function.comp_def] at h
  rw [h]

end ProcedureModel
end Machine
