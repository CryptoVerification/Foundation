import Foundation.Crypto.Semantics.Machine.NativePadPipeline

/-! A reusable secrecy criterion for whole native pipelines, including
variable preparation time. Exact physical handoff erases dependence on the
preparation's internal representation. The remaining public sufficient
information is ciphertext together with actual preparation time. -/
namespace Machine.NativePadPipeline
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} (F : Preparation Input) (O : PolynomialObserver)

/-- Decode the actual first return, keeping its actual time. The decoder is
proof instrumentation and is not an additional runtime loading instruction. -/
noncomputable def preparedCosted (input : Input) : PMF (NativePadEncryption.Input × Nat) :=
  (F.component.firstArrival.procedure.execution.costed input).map (fun result =>
    (F.read input (result.1.resumeAt (F.component.procedure.code.length + 1)), result.2))

noncomputable def cipherTime (input : Input) : PMF (List Bool × Nat) :=
  (preparedCosted F input).map (fun result => (NativePadEncryption.cipher result.1, result.2))

/-- The same fixed continuation consumes a ciphertext/time pair for every
logical input. No preparation-internal tape contents survive this law. -/
noncomputable def publicCosted (information : List Bool × Nat) : PMF (Configuration × Nat) :=
  (NativePadObservation.publicCosted O information.1).map (fun second =>
    ({second.1.resumeAt (link F O).finalPc with halted := true}, information.2 + second.2 + 1))

theorem costed_factorization (input : Input) :
    costed F O input = (cipherTime F input).bind (publicCosted F O) := by
  rw [costed_from_components]
  unfold cipherTime preparedCosted
  rw [PMF.bind_map, PMF.bind_map]
  congr 1
  funext first
  rw [NativePadObservation.costed_public]
  rfl

/-- Equality of ciphertext and actual preparation-time distributions is
sufficient for equality of full final-state/time distributions. -/
theorem costed_eq_of_cipherTime_eq (left right : Input)
    (h : cipherTime F left = cipherTime F right) : costed F O left = costed F O right := by
  rw [costed_factorization, costed_factorization, h]

/-- Randomized and correlated input ensembles use the same continuation. -/
theorem distribution_factorization (inputs : PMF Input) :
    inputs.bind (costed F O) = (inputs.bind (cipherTime F)).bind (publicCosted F O) := by
  rw [PMF.bind_bind]
  congr 1
  funext input
  exact costed_factorization F O input

theorem distribution_eq_of_cipherTime_eq (left right : PMF Input)
    (h : left.bind (cipherTime F) = right.bind (cipherTime F)) :
    left.bind (costed F O) = right.bind (costed F O) := by
  rw [distribution_factorization, distribution_factorization, h]

/-- Every observation of the whole final state and total time inherits the
same equality. No invariance under blank padding is required of the observer. -/
theorem observation_eq_of_cipherTime_eq {Result : Type*} (observe : Configuration × Nat → Result)
    (left right : Input) (h : cipherTime F left = cipherTime F right) :
    (costed F O left).map observe = (costed F O right).map observe := by
  rw [costed_eq_of_cipherTime_eq F O left right h]

/-- The criterion also applies to direct execution with different conservative
analysis horizons, provided each horizon covers its own whole-program bound. -/
theorem run_eq_of_cipherTime_eq (left right : Input) (leftHorizon rightHorizon : Nat)
    (hLeft : timeBound F O left ≤ leftHorizon) (hRight : timeBound F O right ≤ rightHorizon)
    (h : cipherTime F left = cipherTime F right) :
    runToBoundary (stepPMF (fixedCode F O)) Configuration.halted leftHorizon
      (F.component.procedure.execution.entry left) =
    runToBoundary (stepPMF (fixedCode F O)) Configuration.halted rightHorizon
      (F.component.procedure.execution.entry right) := by
  rw [costed_horizon F O left leftHorizon hLeft, costed_horizon F O right rightHorizon hRight]
  exact costed_eq_of_cipherTime_eq F O left right h

end Machine.NativePadPipeline
