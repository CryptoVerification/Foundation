import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyInitialization
import Foundation.Crypto.Logic.Initialization.Interpretation

/-! Reuse the scheme-independent initialization rule for the actual native
two-row authentication-key sampler. Consumers receive its physical store. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (width : Nat → Nat) (n : Nat) (source : Source.Control) (state : State)
    (sourceTrace externalTrace : List (List Bool × List Bool))

noncomputable def initializationProcedure : Procedure (step code oracle) Unit (TableMAC.Key (width n)) :=
  Procedure.ofFixed _
    (fun _ => ⟨state, .initializing source (PrivateKeyGeneration.initial
      (List.replicate (2 * width n) true)), sourceTrace, externalTrace⟩)
    (fun _ key => ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩)
    (fun _ => (TableMAC.scheme width).keygen n) (fun _ => 12 * width n + 5)
    (fun _ => by
      rw [Timing.eval_eq]
      exact initialization_run code oracle width n source state sourceTrace externalTrace)

theorem initializationProcedure_costed :
    (initializationProcedure code oracle width n source state sourceTrace externalTrace).costed () =
      ((TableMAC.scheme width).keygen n).map (fun key => (key, 12 * width n + 5)) := rfl

variable {Output : Type v} {Observed : Type w}
    (consumer : Procedure (step code oracle) (TableMAC.Key (width n)) Output)
    (hEntry : ∀ key, consumer.entry key =
      ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩)
    (cap : Nat) (hCap : ∀ key, consumer.budget key ≤ cap)
    (view : TableMAC.Key (width n) → Output → Observed)

noncomputable def initializedExperiment : CryptoLogic.Initialization.Experiment
    (Input := Unit) (Key := TableMAC.Key (width n)) (Output := Output) (Observed := Observed) (step code oracle) where
  init := initializationProcedure code oracle width n source state sourceTrace externalTrace
  continuation := consumer
  handoff := fun _ key _ => hEntry key
  cap := fun _ => cap
  bound := fun _ key _ => hCap key
  view := view

theorem initializedExperiment_budget :
    (initializedExperiment code oracle width n source state sourceTrace externalTrace consumer hEntry cap hCap view).procedure.budget () =
      12 * width n + 5 + cap := rfl

/-- The existing native sampler is reused through the same pure derivation
as any other initialization. Suffix security includes its actual cost law. -/
theorem initializedExperiment_security
    {RightOutput : Type v}
    (right : Procedure (step code oracle) (TableMAC.Key (width n)) RightOutput)
    (hRightEntry : ∀ key, right.entry key =
      ⟨state, .source (PrivateKeyGeneration.store key) source, sourceTrace, externalTrace⟩)
    (rightCap : Nat) (hRightCap : ∀ key, right.budget key ≤ rightCap)
    (rightView : TableMAC.Key (width n) → RightOutput → Observed)
    (hSuffix : ((TableMAC.scheme width).keygen n).bind (fun key => (consumer.costed key).map
        (fun result => (view key result.1, result.2))) =
      ((TableMAC.scheme width).keygen n).bind (fun key => (right.costed key).map
        (fun result => (rightView key result.1, result.2)))) :
    (initializedExperiment code oracle width n source state sourceTrace externalTrace consumer hEntry cap hCap view).publicCost () =
      (initializedExperiment code oracle width n source state sourceTrace externalTrace right hRightEntry rightCap hRightCap rightView).publicCost () := by
  apply (CryptoLogic.Initialization.sound
    (initializedExperiment code oracle width n source state sourceTrace externalTrace consumer hEntry cap hCap view)
    (initializedExperiment code oracle width n source state sourceTrace externalTrace right hRightEntry rightCap hRightCap rightView)
    () (PMF.pure (12 * width n + 5)) (fun _ => (TableMAC.scheme width).keygen n) ?_ (fun _ => hSuffix)).1
  constructor <;> simp only [initializedExperiment, initializationProcedure_costed, PMF.pure_bind] <;> rfl

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
