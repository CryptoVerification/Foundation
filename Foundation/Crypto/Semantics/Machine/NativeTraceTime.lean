import Foundation.Crypto.Semantics.Machine.NativeFirstArrival

/-! An actual deterministic Step trace cannot include absorbing halt padding.
When the endpoint is halted, its count is the exact first-halt cost, even
when the whole-program contract uses a larger analysis upper bound. -/
namespace Machine
open Foundation.Probability TimedExecution

theorem RunsFor.runToBoundary_eq_pure_of_no_randomBit {code : Program}
    {start finish : Configuration} {steps : Nat} (run : RunsFor code start finish steps)
    (noRandom : ∀ tape, Instruction.randomBit tape ∉ code) :
    runToBoundary (stepPMF code) Configuration.halted steps start = PMF.pure (finish, steps) := by
  induction run with
  | zero => rfl
  | @succ middle finish steps prior last ih =>
      have hActive : middle.halted = false := by
        cases h : middle.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted h) last)
      rw [runToBoundary_add, ih, PMF.pure_bind]
      simp only [runToBoundary, hActive, Bool.false_eq_true, ↓reduceIte,
        stepPMF_eq_pure_of_no_randomBit noRandom last, PMF.pure_bind, PMF.pure_map]

namespace NativeComponent
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

theorem firstArrival_costed_of_trace (input : Input) (finish : Configuration) (steps : Nat)
    (run : RunsFor P.procedure.code (P.procedure.execution.entry input) finish steps)
    (noRandom : ∀ tape, Instruction.randomBit tape ∉ P.procedure.code)
    (halted : finish.halted = true) (bounded : steps ≤ P.procedure.execution.budget input) :
    P.firstArrival.procedure.execution.costed input = PMF.pure (finish, steps) := by
  have hRun := run.runToBoundary_eq_pure_of_no_randomBit noRandom
  rw [P.firstArrival_costed]
  rw [runToBoundary_fuel_stable _ _ steps _ _ bounded (by
    intro result hResult
    rw [hRun, PMF.mem_support_pure_iff] at hResult
    subst result
    exact halted), hRun]

end NativeComponent
end Machine
