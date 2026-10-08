import Foundation.Crypto.Semantics.Machine.NativePadPhysicalPreparation
import Foundation.Crypto.Semantics.Machine.NativePadPipelineObservation

/-! Timing-aware observations for preparation retaining arbitrary blank
padding. We transfer only observations invariant under relative cell
contents, while retaining the actual first-halt time. The separate exact
handoff theorem permits arbitrary observations of finite representations. -/
namespace Machine.NativePadPipeline.PhysicalPreparation
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} (F : PhysicalPreparation Input) (O : PolynomialObserver)

noncomputable def preparedCosted (input : Input) : PMF (NativePadEncryption.Input × Nat) :=
  (F.component.firstArrival.procedure.execution.costed input).map (fun result =>
    (F.read input (result.1.resumeAt (F.component.procedure.code.length + 1)), result.2))

noncomputable def cipherTime (input : Input) : PMF (List Bool × Nat) :=
  (preparedCosted F input).map (fun result => (NativePadEncryption.cipher result.1, result.2))

noncomputable def publicObservation {Result : Type*} (observe : Configuration × Nat → Result)
    (information : List Bool × Nat) : PMF Result :=
  (NativePadObservation.publicCosted O information.1).map (fun second =>
    observe ({second.1.resumeAt (link F O).finalPc with halted := true}, information.2 + second.2 + 1))

/-- Actual blank padding is retained in execution. The canonical state is
used only to evaluate a cell-invariant observation with the same actual time. -/
theorem observation_from_components {Result : Type*} (observe : Configuration × Nat → Result)
    (invariant : ∀ first second time, first.Equivalent second → observe (first, time) = observe (second, time))
    (input : Input) :
    (costed F O input).map observe =
      (F.component.firstArrival.procedure.execution.costed input).bind (fun first =>
        (NativePadObservation.costed O (F.read input (first.1.resumeAt (link F O).entryPc))).map (fun second =>
          observe ({second.1.resumeAt (link F O).finalPc with halted := true}, first.2 + second.2 + 1))) := by
  change ((link F O).component.firstArrival.procedure.execution.costed input).map observe = _
  rw [(link F O).firstArrival_costed_from_components, PMF.map_bind]
  congr 1
  funext first
  rw [PMF.map_comp]
  change ((NativePadObservation.link O).component.equivalentEntries.firstArrival.procedure.execution.costed
    (observerInput F O input (F.read input (first.1.resumeAt (link F O).entryPc)))).map _ = _
  have h := (NativePadObservation.link O).component.equivalentEntries_firstArrival_observation
    (observerInput F O input (F.read input (first.1.resumeAt (link F O).entryPc)))
    (fun second => observe ({second.1.resumeAt (link F O).finalPc with halted := true}, first.2 + second.2 + 1))
    (fun left right time equivalent => invariant _ _ _ ((equivalent.resumeAt _).withHalted true))
  simpa only [observerInput_logical, NativePadObservation.costed, Function.comp_def] using h

theorem observation_factorization {Result : Type*} (observe : Configuration × Nat → Result)
    (invariant : ∀ first second time, first.Equivalent second → observe (first, time) = observe (second, time))
    (input : Input) :
    (costed F O input).map observe = (cipherTime F input).bind (publicObservation F O observe) := by
  rw [observation_from_components F O observe invariant]
  unfold cipherTime preparedCosted
  rw [PMF.bind_map, PMF.bind_map]
  congr 1
  funext first
  rw [NativePadObservation.costed_public]
  rfl

theorem observation_eq_of_cipherTime_eq {Result : Type*} (observe : Configuration × Nat → Result)
    (invariant : ∀ first second time, first.Equivalent second → observe (first, time) = observe (second, time))
    (left right : Input) (h : cipherTime F left = cipherTime F right) :
    (costed F O left).map observe = (costed F O right).map observe := by
  rw [observation_factorization F O observe invariant, observation_factorization F O observe invariant, h]

/-- Exact handoff certificates embed into the physical interface without
changing source code, entries, source costs or logical output distributions. -/
noncomputable def ofExact (F : Preparation Input) : PhysicalPreparation Input where
  component := F.component
  read := F.read
  read_return := F.read_return
  handoff := fun input output h => by
    rw [← F.handoff input output h]
    exact Configuration.Equivalent.refl _
  width := F.width
  width_eq := F.width_eq

theorem ofExact_code (F : Preparation Input) : (ofExact F).component.procedure.code = F.component.procedure.code := rfl

theorem ofExact_costed (F : Preparation Input) (input : Input) :
    (ofExact F).component.procedure.execution.costed input = F.component.procedure.execution.costed input := rfl

end Machine.NativePadPipeline.PhysicalPreparation
