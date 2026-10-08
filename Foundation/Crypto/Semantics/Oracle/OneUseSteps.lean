import Foundation.Crypto.Semantics.ProcedureSteps
import Foundation.Crypto.Semantics.EventCount
import Foundation.Crypto.Semantics.Oracle.OneUseSource

/-! Repeated execution contracts cover the actual controller at every phase.
Issued calls and accepted requests are distinct ghost events. Neither count
changes the physical machine's marginal execution or its charged time. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)

def issued : Control State → Bool
  | .source _ _ frame => match frame.control with
    | .running machine => if machine.halted then false else match code[machine.pc]? with
      | some .call => true
      | _ => false
    | _ => false
  | _ => false

noncomputable def execution (fuel : Nat) := Procedure.steps (step native code oracle) fuel

noncomputable def countedExecution (fuel : Nat) :=
  Procedure.steps (OneUseCounter.countedStep (step native code oracle) (issued code)) fuel

theorem execution_cost (fuel : Nat) (start : Control State) :
    ((execution native code oracle fuel).costed start) =
      (TimedExecution.eval (step native code oracle) fuel start).map (fun result => (result, fuel)) :=
  Procedure.steps_costed (step native code oracle) fuel start

theorem counted_marginal (fuel : Nat) (start : Control State) :
    ((countedExecution native code oracle fuel).semantics (start, 0)).map Prod.fst =
      (execution native code oracle fuel).semantics start := by
  unfold countedExecution execution
  rw [Procedure.steps_semantics, Procedure.steps_semantics]
  exact OneUseCounter.marginal (step native code oracle) (issued code) fuel (start, 0)

theorem issued_bound (fuel : Nat) (start : Control State) (result : Control State × Nat)
    (h : result ∈ ((countedExecution native code oracle fuel).semantics (start, 0)).support) : result.2 ≤ fuel := by
  unfold countedExecution at h
  rw [Procedure.steps_semantics] at h
  exact EventCount.bound (step native code oracle) (issued code) fuel start result h

theorem accepted_bound (fuel : Nat) (start : Control State) (result : Control State × Nat)
    (h : result ∈ ((Procedure.steps (OneUseCounter.countedStep (step native code oracle) accepted) fuel).semantics (start, 0)).support) :
    result.2 ≤ 1 := by
  rw [Procedure.steps_semantics] at h
  exact at_most_one native code oracle fuel start result h
end CryptoOracle.Interactive.OneUseSource
