import Foundation.Crypto.Semantics.Machine.ClosedSubroutineArrival
import Foundation.Crypto.Semantics.Machine.NativeExactClock

/-! Package stored component certificates for a physical native invocation.
The original code's first-halt cost becomes the invocation's first-return
cost, including all state/time correlations and excluding caller steps. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)
    (pre suffix : Program) (returnPc : Nat)
    (layout : ∀ pc, pc < P.procedure.code.length → pre.length + pc ≠ returnPc)

noncomputable def invocation :=
  SubroutineContract.call P.procedure pre suffix returnPc layout P.closed P.entry P.active P.halted

theorem invocation_costed (input : Input) :
    (P.invocation pre suffix returnPc layout).costed input =
      (P.firstArrival.procedure.execution.costed input).map (fun result => (result.1.resumeAt returnPc, result.2)) := by
  unfold invocation
  calc
    _ = (P.firstArrival.procedure.execution.costed input).map
        (fun result => (Program.subroutineState pre.length returnPc result.1, result.2)) := by
      rw [SubroutineContract.call_costed,
        Program.runToBoundary_subroutineState pre P.procedure.code suffix returnPc layout P.closed
          _ (P.entry input) (P.active input), P.firstArrival_costed]
    _ = _ := by
      rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext result hResult
      simp only [Function.comp_def, Program.subroutineState, P.firstArrival_halted input result hResult, ↓reduceIte]

theorem invocation_fixed_time (input : Input) (duration : Nat)
    (fixed : ∀ result, result ∈ (P.firstArrival.procedure.execution.costed input).support → result.2 = duration)
    (result : Configuration × Nat)
    (hResult : result ∈ ((P.invocation pre suffix returnPc layout).costed input).support) : result.2 = duration := by
  rw [P.invocation_costed, PMF.mem_support_map_iff] at hResult
  obtain ⟨original, hOriginal, rfl⟩ := hResult
  exact fixed original hOriginal

theorem invocation_joint_of_clock
    (clock : ExactBoundaryClock (stepPMF P.procedure.code) Configuration.halted)
    (input : Input) (valid : clock.valid (P.procedure.execution.entry input))
    (bounded : clock.remaining (P.procedure.execution.entry input) ≤ P.procedure.execution.budget input) :
    (P.invocation pre suffix returnPc layout).costed input =
      (P.procedure.execution.semantics input).map (fun output =>
        ((P.procedure.execution.exit input output).resumeAt returnPc, clock.remaining (P.procedure.execution.entry input))) := by
  rw [P.invocation_costed, P.firstArrival_joint_of_clock clock input valid bounded, PMF.map_comp, PMF.map_comp]
  rfl

end Machine.NativeComponent
