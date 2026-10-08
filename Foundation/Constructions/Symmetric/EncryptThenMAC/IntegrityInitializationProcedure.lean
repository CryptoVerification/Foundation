import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityInitialization
import Foundation.Crypto.Logic.Initialization.Interpretation

/-! Reuse the scheme-independent initialization rule for the actual native
encryption-key sampler. Consumers receive the actual initialized controller. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (input : List Bool)

noncomputable def initializationProcedure : Procedure (step code oracle) Unit Bool :=
  Procedure.ofFixed _ (fun _ => initial state input)
    (fun _ key => initialized state input key) (fun _ => sampleBit) (fun _ => 3)
    (fun _ => by
      exact initialization_run code oracle state input)

theorem initializationProcedure_costed :
    (initializationProcedure code oracle state input).costed () =
      sampleBit.map (fun key => (key, 3)) := rfl

variable {Output : Type v} {Observed : Type w}
    (consumer : Procedure (step code oracle) Bool Output)
    (hEntry : ∀ key, consumer.entry key =
      initialized state input key)
    (cap : Nat) (hCap : ∀ key, consumer.budget key ≤ cap)
    (view : Bool → Output → Observed)

noncomputable def initializedExperiment : CryptoLogic.Initialization.Experiment
    (Input := Unit) (Key := Bool) (Output := Output) (Observed := Observed) (step code oracle) where
  init := initializationProcedure code oracle state input
  continuation := consumer
  handoff := fun _ key _ => hEntry key
  cap := fun _ => cap
  bound := fun _ key _ => hCap key
  view := view

theorem initializedExperiment_budget :
    (initializedExperiment code oracle state input consumer hEntry cap hCap view).procedure.budget () =
      3 + cap := rfl

/-- The existing native sampler is reused through the same pure derivation
as any other initialization. Suffix security includes its actual cost law. -/
theorem initializedExperiment_security
    {RightOutput : Type v}
    (right : Procedure (step code oracle) Bool RightOutput)
    (hRightEntry : ∀ key, right.entry key =
      initialized state input key)
    (rightCap : Nat) (hRightCap : ∀ key, right.budget key ≤ rightCap)
    (rightView : Bool → RightOutput → Observed)
    (hSuffix : sampleBit.bind (fun key => (consumer.costed key).map
        (fun result => (view key result.1, result.2))) =
      sampleBit.bind (fun key => (right.costed key).map
        (fun result => (rightView key result.1, result.2)))) :
    (initializedExperiment code oracle state input consumer hEntry cap hCap view).publicCost () =
      (initializedExperiment code oracle state input right hRightEntry rightCap hRightCap rightView).publicCost () := by
  apply (CryptoLogic.Initialization.sound
    (initializedExperiment code oracle state input consumer hEntry cap hCap view)
    (initializedExperiment code oracle state input right hRightEntry rightCap hRightCap rightView)
    () (PMF.pure 3) (fun _ => sampleBit) ?_ (fun _ => hSuffix)).1
  constructor <;> simp only [initializedExperiment, initializationProcedure_costed, PMF.pure_bind]

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
