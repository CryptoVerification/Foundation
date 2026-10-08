import Foundation.Examples.ReusableResponseInitializedBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableInitializationEncoded

/-! Register actual key generation and both adaptive requests together with
faithful whole-code/state bit bounds. The same runtime, context and horizon
are used for stopping, game realization and all intermediate peak bounds. -/
namespace Foundation.Examples.ReusableResponseInitializedEncodedBackend
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ReusableResponse.Initialized
open CryptoLogic.General ContractObservedBackend
open ReusableResponseInitializedBackend
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type v} (c : Context State) (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (c.oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

abbrev callerFrame := ReusableResponseInitializedTwoQueries.callerFrame c.state c.trace c.request

def initial : Control State :=
  .initializing (.generating (Machine.Configuration.initial (List.replicate c.width true)))

def measure (code : CryptoOracle.Interactive.Code) (context : Context State) (target : Control State) :=
  ((Encoded.completeEncoding E).encode
    (OneTimePad.keygen, PrivateKeyCopy.code, ReusableResponseTwoQueries.native, code,
      (ReusableResponseInitializedTwoQueries.callerFrame context.state context.trace context.request, target))).length

def capValue := Encoded.bound OneTimePad.keygen ReusableResponseTwoQueries.native ReusableResponseTwoQueries.code
  (Encoded.maxPc (callerFrame c) (initial c)) (Resources.extent stateSize (callerFrame c) (initial c))
  (24 * c.width + 5 * c.request.length + 72) stateIncrement responseCap

def bitCap : Nat → Nat := fun _ => capValue c stateSize stateIncrement responseCap

variable {P : CryptoGoal.{u}} (F : InstanceFamily P)

include hState hOracle in
theorem peak : (profile c P).WithinPeak (runtime State) (measure E)
    (bitCap c stateSize stateIncrement responseCap) F ReusableResponseTwoQueries.code := by
  refine ⟨PolynomiallyBounded.const (capValue c stateSize stateIncrement responseCap), ?_⟩
  intro n side elapsed hElapsed target hTarget
  exact Encoded.encoded_peak E stateSize hState OneTimePad.keygen ReusableResponseTwoQueries.native
    ReusableResponseTwoQueries.code c.oracle (callerFrame c) stateIncrement responseCap hOracle
    (24 * c.width + 5 * c.request.length + 72) elapsed hElapsed (initial c) target hTarget

include hState in
theorem family_peak (contexts : ∀ n, P.Instance n → Bool → Context State)
    (horizon initialPc initialExtent increments responses : Nat → Nat)
    (hTime : PolynomiallyBounded horizon) (hPc : PolynomiallyBounded initialPc)
    (hExtent : PolynomiallyBounded initialExtent) (hIncrement : PolynomiallyBounded increments)
    (hResponse : PolynomiallyBounded responses)
    (hAddress : ∀ n side, Encoded.maxPc (callerFrame (contexts n (F n) side)) (initial (contexts n (F n) side)) ≤ initialPc n)
    (hInitial : ∀ n side, Resources.extent stateSize (callerFrame (contexts n (F n) side))
      (initial (contexts n (F n) side)) ≤ initialExtent n)
    (hFamilyOracle : ∀ n side state request result,
      result ∈ ((contexts n (F n) side).oracle state request).support →
      stateSize result.1 ≤ stateSize state + increments n ∧ result.2.length ≤ responses n) :
    (familyProfile contexts horizon).WithinPeak (runtime State) (measure E)
      (fun n => Encoded.bound OneTimePad.keygen ReusableResponseTwoQueries.native ReusableResponseTwoQueries.code
        (initialPc n) (initialExtent n) (horizon n) (increments n) (responses n)) F ReusableResponseTwoQueries.code := by
  refine ⟨Encoded.bound_polynomial _ _ _ hPc hExtent hTime hIncrement hResponse, ?_⟩
  intro n side elapsed hElapsed target hTarget
  have hp := Encoded.encoded_peak E stateSize hState OneTimePad.keygen ReusableResponseTwoQueries.native
    ReusableResponseTwoQueries.code (contexts n (F n) side).oracle (callerFrame (contexts n (F n) side))
    (increments n) (responses n) (hFamilyOracle n side) (horizon n) elapsed hElapsed
    (initial (contexts n (F n) side)) target hTarget
  exact hp.trans (Encoded.bound_mono_initial _ _ _ (hAddress n side) (hInitial n side) (horizon n) (increments n) (responses n))

variable (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

include hState hOracle in
noncomputable def witness (A : AdversaryFamily P F)
    (hModel : ∀ n side, PMF.pure false = modelGame F A n side) :
    (peakRegistration (runtime State) modelGame hAdvantage (measure E)).object.Witness F A :=
  peakWitness (runtime State) modelGame hAdvantage (measure E) F A ReusableResponseTwoQueries.code
    (profile c P) (bitCap c stateSize stateIncrement responseCap)
    (executes c F) (peak c E stateSize hState stateIncrement responseCap hOracle F) hModel

end Foundation.Examples.ReusableResponseInitializedEncodedBackend
