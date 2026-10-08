import Foundation.Examples.OneUseAdaptiveEcho
import Foundation.Crypto.Logic.General.OneUseObservedBackend
import Foundation.Crypto.Logic.General.OneUseStorageObservedBackend
import Foundation.Crypto.Logic.General.OneUseEncodedObservedBackend

/-! Register the actual finite adaptive echo caller with polynomial time and
complete retained-data evidence. Both experiment sides may choose different
messages. Observers must respect the physical/logical state correspondence;
this resource adapter does not itself assert secrecy of arbitrary observers. -/
namespace Foundation.OneUseAdaptiveEchoExamples.Resources
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive CryptoLogic.General
universe u v
set_option backward.isDefEq.respectTransparency false
variable {P : CryptoGoal.{u}} {State : Type v}
    (width : Nat → Nat) (message : ∀ n, Bool → Bits (width n)) (input : Nat → List Bool)
    (state : Nat → State) (trace : Nat → List (List Bool × List Bool)) (stateSize : State → Nat)
    (oracle : Nat → Bool → BitOracle State)
    (readPhysical : Nat → Bool → OneUseInitialization.Control State → Bool)
    (readLogical : Nat → Bool → OneUseSourceRounds.Boundary State → Bool)

noncomputable def sourceProfile : OneUseObservedBackend.Profile P State where
  width := width
  stateSize := stateSize
  oracle := fun n _ side => oracle n side
  caller := fun n _ side => (initial (message n side) (input n) (state n) (trace n)).frame
  logicalBound := fun _ => 3
  cap := fun n => consumerCap (width n) (input n) (state n) (trace n) stateSize
  horizon := fun n => 105 * width n + 99 * uniformExtent (width n) (input n) (state n) (trace n) stateSize + 305
  readPhysical := fun n _ side => readPhysical n side
  readLogical := fun n _ side => readLogical n side

theorem source_executes (F : InstanceFamily P)
    (hWidth : PolynomiallyBounded width)
    (hExtent : PolynomiallyBounded (fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize))
    (hRead : ∀ n side (key : Bits (width n)) source,
      readPhysical n side (.active (OneUseSourceRounds.embed (OneUseProgramInitialization.store key) source)) =
        readLogical n side source) :
    (sourceProfile width message input state trace stateSize oracle readPhysical readLogical).ExecutesWithin F code := by
  refine ⟨initialized_time_profile_polynomial hWidth hExtent, ?_⟩
  intro n side
  refine ⟨?_, ?_, hRead n side⟩
  · change 6 * width n + 5 + consumerCap (width n) (input n) (state n) (trace n) stateSize ≤
      105 * width n + 99 * uniformExtent (width n) (input n) (state n) (trace n) stateSize + 305
    unfold consumerCap
    omega
  · refine ⟨(fun key => callerCertificate key (message n side) (input n) (state n) (trace n) (oracle n side) stateSize), ?_, ?_⟩
    · intro key
      exact callerCertificate_cap key (message n side) (input n) (state n) (trace n) (oracle n side) stateSize
    · intro key
      rfl

def storageProfile (stateIncrement responseCap : Nat → Nat) : OneUseStorageObservedBackend.StorageProfile State where
  stateSize := stateSize
  initialCap := fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize
  stateIncrement := stateIncrement
  responseCap := responseCap

theorem storage_certificate (F : InstanceFamily P) (stateIncrement responseCap : Nat → Nat)
    (hExtent : PolynomiallyBounded (fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize))
    (hIncrement : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap)
    (hOracle : ∀ n side start request result, result ∈ (oracle n side start request).support →
      stateSize result.1 ≤ stateSize start + stateIncrement n ∧ result.2.length ≤ responseCap n) :
    (storageProfile width input state trace stateSize stateIncrement responseCap).Certificate
      (sourceProfile width message input state trace stateSize oracle readPhysical readLogical).toContract F where
  initialPolynomial := hExtent
  incrementPolynomial := hIncrement
  responsePolynomial := hResponse
  initialBound := fun n side => initial_extent_le_uniform (message n side) (input n) (state n) (trace n) stateSize
  oracleBound := hOracle

noncomputable def combined (stateIncrement responseCap : Nat → Nat) : OneUseStorageObservedBackend.Resources P State where
  execution := (sourceProfile width message input state trace stateSize oracle readPhysical readLogical).toContract
  storage := storageProfile width input state trace stateSize stateIncrement responseCap

theorem combined_executes (F : InstanceFamily P) (stateIncrement responseCap : Nat → Nat)
    (hWidth : PolynomiallyBounded width)
    (hExtent : PolynomiallyBounded (fun n => uniformExtent (width n) (input n) (state n) (trace n) stateSize))
    (hIncrement : PolynomiallyBounded stateIncrement) (hResponse : PolynomiallyBounded responseCap)
    (hRead : ∀ n side (key : Bits (width n)) source,
      readPhysical n side (.active (OneUseSourceRounds.embed (OneUseProgramInitialization.store key) source)) =
        readLogical n side source)
    (hOracle : ∀ n side start request result, result ∈ (oracle n side start request).support →
      stateSize result.1 ≤ stateSize start + stateIncrement n ∧ result.2.length ≤ responseCap n) :
    let r := combined (P := P) width message input state trace stateSize oracle readPhysical readLogical stateIncrement responseCap
    r.execution.ExecutesWithin Machine.OneTimePad.Prepared.listProcedure.code F code ∧ r.storage.Certificate r.execution F := by
  constructor
  · exact OneUseObservedBackend.Profile.toContract_executes _ F code
      (source_executes width message input state trace stateSize oracle readPhysical readLogical F hWidth hExtent hRead)
  · exact storage_certificate width message input state trace stateSize oracle readPhysical readLogical F
      stateIncrement responseCap hExtent hIncrement hResponse hOracle

/-- The registered logical game retains the real final caller state and its
adaptive transcript, rather than declaring an unrelated model experiment. -/
theorem logicalGame_eq (F : InstanceFamily P) (stateIncrement responseCap : Nat → Nat)
    (n : Nat) (side : Bool) :
    (combined (P := P) width message input state trace stateSize oracle readPhysical readLogical
      stateIncrement responseCap).execution.logicalGame F code n side =
      (uniform (Bits (width n))).map (fun key =>
        readLogical n side (halted key (message n side) (input n) (state n) (trace n))) := by
  change (uniform (Bits (width n))).bind (fun key =>
    (TimedExecution.eval (OneUseSourceRounds.callerStep code (oracle n side) key.toList []) 3
      (initial (message n side) (input n) (state n) (trace n))).map (readLogical n side)) = _
  simp_rw [caller_run]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- The caller enters at address zero, for every width and both message sides. -/
def encodingProfile (E : Machine.FiniteBitEncoding State) : OneUseEncodedObservedBackend.EncodingProfile State where
  encoding := E
  initialAddress := fun _ => 0

theorem encoding_certificate (F : InstanceFamily P) (stateIncrement responseCap : Nat → Nat)
    (E : Machine.FiniteBitEncoding State) (hState : ∀ state, (E.encode state).length ≤ stateSize state) :
    (encodingProfile E).Certificate
      (combined (P := P) width message input state trace stateSize oracle readPhysical readLogical
        stateIncrement responseCap) F where
  stateBound := hState
  addressPolynomial := PolynomiallyBounded.const 0
  addressBound := fun _ _ => Nat.le_refl 0

end Foundation.OneUseAdaptiveEchoExamples.Resources
