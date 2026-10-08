import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyInitializationProcedure
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceObservation
import Foundation.Constructions.Symmetric.EncryptThenMAC.NativePrivacyGame
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitSecurity
import Foundation.Crypto.Semantics.ProcedureDispatch

/-! Reuse the common initialization/consumer contract for the complete native
privacy reduction. The source continuation includes all queries, physical
signing, response delivery, and actual source halt. Its fixed duration is the
common padded horizon, not a claim about first-arrival halting time. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (width : Nat → Nat) (n count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key : TableMAC.Key (width n),
      CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key)
        (logicalInitial state input).view count)

noncomputable def sourceProcedure : Procedure (step code oracle)
    (TableMAC.Key (width n)) (LogicalFrame State) :=
  Procedure.dispatch (fun key : TableMAC.Key (width n) =>
    Procedure.ofFixed _
      (fun _ : Unit => (logicalInitial state input).embed key)
      (fun _ output => output.embed key)
      (fun _ => TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input))
      (fun _ => count * (29 * width n + 39))
      (fun _ => by
        rw [Timing.eval_eq]
        exact realized_source_execution code oracle key count (logicalInitial state input) (hStops key)))

theorem sourceProcedure_entry (key : TableMAC.Key (width n)) :
    (sourceProcedure code oracle width n count state input hStops).entry key =
      ⟨state, .source (PrivateKeyGeneration.store key) (.running (Configuration.initial input)), [], []⟩ := rfl

theorem sourceProcedure_budget (key : TableMAC.Key (width n)) :
    (sourceProcedure code oracle width n count state input hStops).budget key = count * (29 * width n + 39) := rfl

theorem sourceProcedure_costed (key : TableMAC.Key (width n)) :
    (sourceProcedure code oracle width n count state input hStops).costed key =
      (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map
        (fun output => (output, count * (29 * width n + 39))) := rfl

noncomputable def sourceExperiment :=
  initializedExperiment code oracle width n (.running (Configuration.initial input)) state [] []
    (sourceProcedure code oracle width n count state input hStops)
    (sourceProcedure_entry code oracle width n count state input hStops)
    (count * (29 * width n + 39))
    (fun key => le_of_eq (sourceProcedure_budget code oracle width n count state input hStops key))
    (fun _ output => PrivacyGameCodec.guess output.control)

theorem sourceExperiment_budget :
    (sourceExperiment code oracle width n count state input hStops).procedure.budget () =
      executionBudget (width n) count := rfl

/-- Exact whole native experiment and its charged common horizon. Neither
private authentication keys nor proof-only layout indices are observed. -/
theorem sourceExperiment_publicCost :
    (sourceExperiment code oracle width n count state input hStops).publicCost () =
      (eval code oracle (executionBudget (width n) count)
        (initial state (List.replicate (2 * width n) true) input)).map
          (fun final => (PrivacyGameCodec.nativeGuess final, executionBudget (width n) count)) := by
  rw [initialized_source_execution code oracle width n count state input
    (fun key _ => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key))]
  simp only [sourceExperiment, initializedExperiment, CryptoLogic.Initialization.Experiment.publicCost,
    CryptoLogic.Initialization.Experiment.procedure, Procedure.seq, initializationProcedure_costed,
    sourceProcedure_costed, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- Logical source security is transported by the same pure initialization
rule to the full native experiments, including their common padded cost. -/
theorem sourceExperiment_security (rightCode : Source.Code)
    (rightOracle : CryptoOracle.Interactive.BitOracle State) (rightState : State) (rightInput : List Bool)
    (rightStops : ∀ key : TableMAC.Key (width n),
      CryptoOracle.Interactive.Reification.HaltsWithin rightCode (authenticatedOracle rightOracle key)
        (logicalInitial rightState rightInput).view count)
    (hSuffix : ((TableMAC.scheme width).keygen n).bind (fun key =>
      (TimedExecution.eval (logicalStep code oracle key) count (logicalInitial state input)).map
        (fun output => PrivacyGameCodec.guess output.control)) =
      ((TableMAC.scheme width).keygen n).bind (fun key =>
      (TimedExecution.eval (logicalStep rightCode rightOracle key) count (logicalInitial rightState rightInput)).map
        (fun output => PrivacyGameCodec.guess output.control))) :
    (sourceExperiment code oracle width n count state input hStops).publicCost () =
      (sourceExperiment rightCode rightOracle width n count rightState rightInput rightStops).publicCost () := by
  apply (CryptoLogic.Initialization.sound
    (sourceExperiment code oracle width n count state input hStops)
    (sourceExperiment rightCode rightOracle width n count rightState rightInput rightStops)
    () (PMF.pure (12 * width n + 5)) (fun _ => (TableMAC.scheme width).keygen n) ?_ ?_).1
  · constructor <;> simp only [sourceExperiment, initializedExperiment,
      initializationProcedure_costed, PMF.pure_bind] <;> rfl
  · intro _
    have h := congrArg (fun distribution => distribution.map
      (fun bit => (bit, count * (29 * width n + 39)))) hSuffix
    simp only [sourceExperiment, initializedExperiment, sourceProcedure_costed,
      PMF.map_bind, PMF.map_comp, Function.comp_def] at h ⊢
    convert h using 1 <;> rfl

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
