import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityInitializationProcedure
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceExecution
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Reusable initialization and source contracts for the native integrity
reduction. The observation is arbitrary; the charged cost is a padded horizon,
not the first-arrival halting time. Tag lengths and stopping require evidence. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : SourceCode)
    (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat)
    (state : State) (input : List Bool)
    (hStops : ∀ key : Bool,
      ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true)

noncomputable def sourceProcedure : Procedure (step code oracle) Bool (LogicalFrame State) :=
  Procedure.dispatch (fun key : Bool =>
    Procedure.ofFixed _ (fun _ : Unit => (logicalInitial state input).embed key)
      (fun _ output => output.embed key)
      (fun _ => TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input))
      (fun _ => count * (5 * width + 36))
      (fun _ => by
        exact source_execution code oracle key width hTags count (logicalInitial state input)
          (hStops key) _ (Nat.le_refl _)))

theorem sourceProcedure_entry (key : Bool) :
    (sourceProcedure code oracle width hTags count state input hStops).entry key =
      initialized state input key := rfl

theorem sourceProcedure_costed (key : Bool) :
    (sourceProcedure code oracle width hTags count state input hStops).costed key =
      (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map
        (fun output => (output, count * (5 * width + 36))) := rfl

variable {Observed : Type v} (observe : Frame State → Observed)

noncomputable def sourceExperiment :=
  initializedExperiment code oracle state input
    (sourceProcedure code oracle width hTags count state input hStops)
    (sourceProcedure_entry code oracle width hTags count state input hStops)
    (count * (5 * width + 36)) (fun _ => Nat.le_refl _)
    (fun key output => observe (output.embed key))

theorem sourceExperiment_budget :
    (sourceExperiment code oracle width hTags count state input hStops observe).procedure.budget () =
      executionBudget width count := rfl

/-- Exact physical execution, including native key generation, adaptive
queries, delivery, both histories and source termination. -/
theorem sourceExperiment_publicCost :
    (sourceExperiment code oracle width hTags count state input hStops observe).publicCost () =
      (eval code oracle (executionBudget width count) (initial state input)).map
        (fun final => (observe final, executionBudget width count)) := by
  rw [initialized_source_execution code oracle width hTags count state input
    (fun key _ => hStops key)]
  simp only [sourceExperiment, initializedExperiment, CryptoLogic.Initialization.Experiment.publicCost,
    CryptoLogic.Initialization.Experiment.procedure, Procedure.seq, initializationProcedure_costed,
    sourceProcedure_costed, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- A source comparison with any chosen observation is lifted by the pure
initialization rule; no observation of private state is silently discarded. -/
theorem sourceExperiment_security (rightCode : SourceCode)
    (rightOracle : State → Bool → PMF (State × List Bool))
    (rightTags : TagLength rightOracle width) (rightState : State) (rightInput : List Bool)
    (rightStops : ∀ key : Bool,
      ∀ final ∈ (TimedExecution.eval (logicalStep rightCode rightOracle key) count
        (logicalInitial rightState rightInput)).support,
        CryptoOracle.Interactive.Reification.terminal final.control = true)
    (rightObserve : Frame State → Observed)
    (hSuffix : sampleBit.bind (fun key =>
      (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map
        (fun output => observe (output.embed key))) =
      sampleBit.bind (fun key =>
        (TimedExecution.eval (logicalStep rightCode rightOracle key) count
          (logicalInitial rightState rightInput)).map
          (fun output => rightObserve (output.embed key)))) :
    (sourceExperiment code oracle width hTags count state input hStops observe).publicCost () =
      (sourceExperiment rightCode rightOracle width rightTags count rightState rightInput
        rightStops rightObserve).publicCost () := by
  apply (CryptoLogic.Initialization.sound
    (sourceExperiment code oracle width hTags count state input hStops observe)
    (sourceExperiment rightCode rightOracle width rightTags count rightState rightInput rightStops rightObserve)
    () (PMF.pure 3) (fun _ => sampleBit) ?_ ?_).1
  · constructor <;> simp only [sourceExperiment, initializedExperiment,
      initializationProcedure_costed, PMF.pure_bind]
  · intro _
    have h := congrArg (fun distribution => distribution.map
      (fun output => (output, count * (5 * width + 36)))) hSuffix
    simp only [sourceExperiment, initializedExperiment, sourceProcedure_costed,
      PMF.map_bind, PMF.map_comp, Function.comp_def] at h ⊢
    exact h

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
