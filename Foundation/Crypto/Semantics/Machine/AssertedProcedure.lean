import Foundation.Crypto.Semantics.Machine.ProgramAssertions
import Foundation.Crypto.Semantics.Machine.RelationalProcedure
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Derive input-dependent typed postconditions from verified local program
assertions. Operational reachability is explicit: a residual execution law
alone need not justify treating reported endpoints as actual reached states. -/
namespace Machine.AssertedProcedure
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v}
    (P : Machine.Procedure Input Output) (assertions : Input → Program.Assertions)
    (verified : ∀ input, (assertions input).Verified P.code)
    (hEntry : ∀ input, (assertions input).Holds (P.execution.entry input))
    (hOperational : TimedExecution.Procedure.Operational P.execution)

include verified hEntry hOperational

/-- The invariant holds at the actual costed endpoint, without assuming halt. -/
theorem costed_endpoint (input : Input) (result : Output × Nat)
    (h : result ∈ (P.execution.costed input).support) :
    (assertions input).Holds (P.execution.exit input result.1) :=
  eval_preserves _ _ (verified input).preserves result.2 _ _ (hEntry input)
    (hOperational input result h)

/-- Every supported output has an actual cost witness. -/
theorem supported_endpoint (input : Input) (output : Output)
    (h : output ∈ (P.execution.semantics input).support) :
    (assertions input).Holds (P.execution.exit input output) := by
  rw [← P.execution.correct input, PMF.mem_support_map_iff] at h
  obtain ⟨result, hr, rfl⟩ := h
  exact costed_endpoint P assertions verified hEntry hOperational input result hr

noncomputable def native : Machine.Procedure Input (RelationalProcedure.Result
    (fun input machine => (assertions input).Holds machine)) :=
  RelationalProcedure.native P _ (supported_endpoint P assertions verified hEntry hOperational)

theorem code : (native P assertions verified hEntry hOperational).code = P.code := rfl

theorem entry (input : Input) :
    (native P assertions verified hEntry hOperational).execution.entry input = P.execution.entry input := rfl

theorem budget (input : Input) :
    (native P assertions verified hEntry hOperational).execution.budget input = P.execution.budget input := rfl

/-- Certification preserves the entire physical endpoint/time distribution. -/
theorem costed (input : Input) :
    ((native P assertions verified hEntry hOperational).execution.costed input).map
      (fun result => (result.1.val.2, result.2)) =
      (P.execution.costed input).map (fun result => (P.execution.exit input result.1, result.2)) :=
  RelationalProcedure.costed P _ (supported_endpoint P assertions verified hEntry hOperational) input

end Machine.AssertedProcedure
