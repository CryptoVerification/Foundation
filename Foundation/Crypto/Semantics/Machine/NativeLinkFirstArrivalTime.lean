import Foundation.Crypto.Semantics.Machine.NativeLinkArrivalTime
import Foundation.Crypto.Semantics.ProcedureFixedTime
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! Certify that a fixed-time link reports its actual first global halt.
The body is still active at its exact completion time; the caller halt is
one further transition. An explicit budget condition makes the residual
law available at the body horizon. No absorbing padding is counted. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput} (L : Link P Q)

theorem body_fixed_time (input : Input) (firstTime secondTime : Nat)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime)
    (result : ((Input × Output) × Configuration) × Nat)
    (hResult : result ∈ (L.body.costed input).support) : result.2 = firstTime + secondTime := by
  change result ∈ ((L.first.costed input).bind (fun middle =>
    (L.second.costed middle.1).map (fun output => ((middle.1, output.1), middle.2 + output.2)))).support at hResult
  rw [PMF.mem_support_bind_iff] at hResult
  obtain ⟨middle, hMiddle, hRest⟩ := hResult
  rw [PMF.mem_support_map_iff] at hRest
  obtain ⟨output, hOutput, rfl⟩ := hRest
  rw [fixedFirst middle hMiddle, fixedSecond middle hMiddle output hOutput]

theorem body_active (input : Input) (result : (Input × Output) × Configuration)
    (hResult : result ∈ (L.body.semantics input).support) :
    (L.body.exit input result).halted = false := by
  change result ∈ ((L.first.semantics input).bind (fun middle =>
    (L.second.semantics middle).map (fun output => (middle, output)))).support at hResult
  rw [PMF.mem_support_bind_iff] at hResult
  obtain ⟨middle, _, hRest⟩ := hResult
  rw [PMF.mem_support_map_iff] at hRest
  obtain ⟨machine, hMachine, rfl⟩ := hRest
  change machine ∈ ((Q.execution.semantics (L.adapt middle.1 middle.2)).map
    (fun output => (Q.execution.exit (L.adapt middle.1 middle.2) output).resumeAt L.finalPc)).support at hMachine
  rw [PMF.mem_support_map_iff] at hMachine
  obtain ⟨output, _, rfl⟩ := hMachine
  rfl

theorem firstArrival_joint_of_fixed_time (input : Input) (firstTime secondTime : Nat)
    (bounded : P.execution.budget input + L.cap input ≤ firstTime + secondTime)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime) :
    L.component.firstArrival.procedure.execution.costed input =
      (L.native.execution.semantics input).map (fun state => (state, firstTime + secondTime + 1)) := by
  have hBody := L.body.eval_at_fixed_time input (firstTime + secondTime) bounded
    (L.body_fixed_time input firstTime secondTime fixedFirst fixedSecond)
  have hActive : ∀ state ∈ (eval (stepPMF L.code) (firstTime + secondTime)
      (L.native.execution.entry input)).support, state.halted = false := by
    intro state hState
    change state ∈ (eval (stepPMF L.code) (firstTime + secondTime) (L.body.entry input)).support at hState
    rw [hBody, PMF.mem_support_map_iff] at hState
    obtain ⟨result, hResult, rfl⟩ := hState
    exact L.body_active input result hResult
  have hRun := L.native.execution.eval_at_fixed_time input (firstTime + secondTime + 1)
    (by rw [L.budget]; omega) (L.fixed_time input firstTime secondTime fixedFirst fixedSecond)
  have hEval : eval (stepPMF L.code) (firstTime + secondTime + 1)
      (L.native.execution.entry input) = L.native.execution.semantics input := by
    change eval (stepPMF L.code) (firstTime + secondTime + 1)
      (L.native.execution.entry input) = (L.native.execution.semantics input).map id at hRun
    simpa only [PMF.map_id] using hRun
  have hComplete : ∀ state ∈ (eval (stepPMF L.code) (firstTime + secondTime + 1)
      (L.native.execution.entry input)).support, state.halted = true := by
    rw [hEval]
    exact L.halted input
  have h := runToBoundary_joint_of_adjacent (stepPMF L.code) Configuration.halted
    (L.native.execution.entry input) (firstTime + secondTime)
    (fun state hHalt => by simp [stepPMF, next, hHalt]) hActive hComplete
  have hHorizon := L.component.firstArrival_costed_horizon input (firstTime + secondTime + 1)
    (by change P.execution.budget input + L.cap input + 1 ≤ _; omega)
  change runToBoundary (stepPMF L.code) Configuration.halted (firstTime + secondTime + 1)
    (L.native.execution.entry input) = L.component.firstArrival.procedure.execution.costed input at hHorizon
  rw [hHorizon, hEval] at h
  exact h

theorem firstArrival_costed_eq_of_fixed_time (input : Input) (firstTime secondTime : Nat)
    (bounded : P.execution.budget input + L.cap input ≤ firstTime + secondTime)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime) :
    L.component.firstArrival.procedure.execution.costed input = L.native.execution.costed input := by
  rw [L.firstArrival_joint_of_fixed_time input firstTime secondTime bounded fixedFirst fixedSecond,
    L.joint_of_fixed_time input firstTime secondTime fixedFirst fixedSecond]

end Machine.TypedNativeComposition.Link
