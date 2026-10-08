import Foundation.Crypto.Semantics.Machine.TypedNativeComposition
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability

/-! Native composition reports actual reached endpoints at the reported
costs. Boundary calls derive reachability from their actual first-arrival
execution, without assuming reachability from a residual law alone. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {State : Type u} {Target : Type v} {Input : Type w} {Output : Type x}
    {sourceStep : State → PMF State}

theorem operational_transport (P : Procedure sourceStep Input Output) (hP : Operational P)
    (targetStep : Target → PMF Target) (embed : State → Target)
    (hStep : ∀ state, targetStep (embed state) = (sourceStep state).map embed) :
    Operational (P.transport targetStep embed hStep) := by
  intro input result hResult
  change embed (P.exit input result.1) ∈
    (eval targetStep result.2 (embed (P.entry input))).support
  rw [← eval_map sourceStep targetStep embed (fun state => (hStep state).symm),
    PMF.mem_support_map_iff]
  exact ⟨P.exit input result.1, hP input result hResult, rfl⟩

end Foundation.Probability.TimedExecution.Procedure

namespace Machine.SubroutineContract
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v}
    (P : Machine.Procedure Input Output) (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < P.code.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ start target, start.pc < P.code.length → Step P.code start target →
      target.halted = false → target.pc < P.code.length)
    (hEntry : ∀ input, (P.execution.entry input).pc < P.code.length)
    (hActive : ∀ input, (P.execution.entry input).halted = false)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)

theorem operational : TimedExecution.Procedure.Operational
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt) := by
  intro input result hResult
  rw [call_costed] at hResult
  exact runToBoundary_reachable _ _ _ _ result hResult

namespace Typed
variable (read : Input → Configuration → Output)
    (hRead : ∀ input output, output ∈ (P.execution.semantics input).support →
      read input ((P.execution.exit input output).resumeAt returnPc) = output)

theorem operational : TimedExecution.Procedure.Operational
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt read hRead) := by
  unfold call
  apply TimedExecution.Procedure.operational_observe
  apply TimedExecution.Procedure.operational_remember
  exact SubroutineContract.operational P pre suffix returnPc hLayout hClosed hEntry hActive hHalt

end Typed
end Machine.SubroutineContract

namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q)

theorem first_operational : TimedExecution.Procedure.Operational L.first := by
  unfold first
  apply TimedExecution.Procedure.operational_transport
  apply SubroutineContract.Typed.operational

theorem second_operational : TimedExecution.Procedure.Operational L.second := by
  unfold second
  apply TimedExecution.Procedure.operational_transport
  apply TimedExecution.Procedure.operational_reindex
  apply SubroutineContract.operational

theorem halt_operational : TimedExecution.Procedure.Operational L.halt := by
  unfold halt
  apply TimedExecution.Procedure.operational_ofFixed

theorem body_operational : TimedExecution.Procedure.Operational L.body := by
  unfold body
  apply TimedExecution.Procedure.operational_seq
  · exact L.first_operational
  · exact L.second_operational

/-- No additional reachability premise on the component contracts is
needed: the compiled calls execute their actual first-return procedures. -/
theorem operational : TimedExecution.Procedure.Operational L.native.execution := by
  change TimedExecution.Procedure.Operational L.execution
  unfold execution
  apply TimedExecution.Procedure.operational_physical
  apply TimedExecution.Procedure.operational_seq
  · exact L.body_operational
  · apply TimedExecution.Procedure.operational_reindex
    exact L.halt_operational

end Machine.TypedNativeComposition.Link
