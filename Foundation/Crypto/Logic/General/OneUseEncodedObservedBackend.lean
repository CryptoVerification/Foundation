import Foundation.Crypto.Logic.General.OneUseStorageObservedBackend
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Strengthen the observed finite-code class with faithful bit encodings of
all three programs and every private runtime state. The execution clock is
still the physical controller clock, not a bit-encoding interpreter clock. -/
namespace CryptoLogic.General.OneUseEncodedObservedBackend
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
universe u v
set_option backward.isDefEq.respectTransparency false

structure EncodingProfile (State : Type v) where
  encoding : Machine.FiniteBitEncoding State
  initialAddress : Nat → Nat

namespace EncodingProfile
variable {P : CryptoGoal.{u}} {State : Type v}
    (e : EncodingProfile State) (r : OneUseStorageObservedBackend.Resources P State)

structure Certificate (F : InstanceFamily P) : Prop where
  stateBound : ∀ state, (e.encoding.encode state).length ≤ r.storage.stateSize state
  addressPolynomial : PolynomiallyBounded e.initialAddress
  addressBound : ∀ n side, PrivateControllerEncoding.initializationMaxPc
    (r.execution.caller n (F n) side)
    (.initializing (.generating (Machine.Configuration.initial (List.replicate (r.execution.width n) true)))) ≤
      e.initialAddress n

def bound (native : Machine.Program) (code : Code) (n : Nat) : Nat :=
  PrivateControllerEncoding.encodedBound Machine.OneTimePad.keygen native code (e.initialAddress n)
    (r.storage.initialCap n) (r.execution.horizon n) (r.storage.stateIncrement n) (r.storage.responseCap n)

theorem bound_polynomial (native : Machine.Program) (code : Code) (F : InstanceFamily P)
    (hEncoding : e.Certificate r F) (hStorage : r.storage.Certificate r.execution F)
    (hTime : PolynomiallyBounded r.execution.horizon) : PolynomiallyBounded (e.bound r native code) :=
  PrivateControllerEncoding.encodedBound_polynomial _ _ _ hEncoding.addressPolynomial
    hStorage.initialPolynomial hTime hStorage.incrementPolynomial hStorage.responsePolynomial

theorem encoded_peak (native : Machine.Program) (code : Code) (F : InstanceFamily P)
    (hEncoding : e.Certificate r F) (hStorage : r.storage.Certificate r.execution F)
    (n : Nat) (side : Bool) (elapsed : Nat) (hElapsed : elapsed ≤ r.execution.horizon n)
    (target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen native code
        (r.execution.oracle n (F n) side) (r.execution.caller n (F n) side)) elapsed
      (.initializing (.generating (Machine.Configuration.initial (List.replicate (r.execution.width n) true))))).support) :
    ((PrivateControllerEncoding.completeEncoding e.encoding).encode
      (Machine.OneTimePad.keygen, native, code,
        PrivateControllerEncoding.runtime (r.execution.caller n (F n) side) target)).length ≤
      e.bound r native code n := by
  have hp := PrivateControllerEncoding.encoded_peak e.encoding r.storage.stateSize hEncoding.stateBound
    Machine.OneTimePad.keygen native code (r.execution.oracle n (F n) side) (r.execution.caller n (F n) side)
    (r.storage.stateIncrement n) (r.storage.responseCap n) (hStorage.oracleBound n side)
    (r.execution.horizon n) elapsed hElapsed _ target hTarget
  exact hp.trans (PrivateControllerEncoding.encodedBound_mono_initial _ _ _
    (hEncoding.addressBound n side) (hStorage.initialBound n side) _ _ _)

end EncodingProfile

structure Resources (P : CryptoGoal.{u}) (State : Type v) where
  retained : OneUseStorageObservedBackend.Resources P State
  encoded : EncodingProfile State

variable {P : CryptoGoal.{u}} {State : Type v}

noncomputable def registration (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true))) :
    ObservedExecution Backends.system .interactive P where
  Resources := Resources P State
  ExecutesWithin := fun F code r => r.retained.execution.ExecutesWithin native F code ∧
    r.retained.storage.Certificate r.retained.execution F ∧ r.encoded.Certificate r.retained F
  game := fun F code r => r.retained.execution.nativeGame native F code
  modelGame := modelGame
  advantage_eq := hAdvantage

variable (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

def witness (F A) (code : Code) (r : Resources P State)
    (hExec : r.retained.execution.ExecutesWithin native F code)
    (hStorage : r.retained.storage.Certificate r.retained.execution F)
    (hEncoding : r.encoded.Certificate r.retained F)
    (hLogical : ∀ n side, r.retained.execution.logicalGame F code n side = modelGame F A n side) :
    (registration (State := State) native modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration (State := State) native modelGame hAdvantage).Realizes F A code r := by
    intro n side
    exact (r.retained.execution.nativeGame_eq native F code hExec n side).trans (hLogical n side)
  exact ⟨code, r, ⟨hExec, hStorage, hEncoding⟩, hReal,
    ⟨code, r, ⟨hExec, hStorage, hEncoding⟩, hReal⟩⟩

def forgetEncoding (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A) :
    (OneUseStorageObservedBackend.registration (State := State) native modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, W.resources.retained, ⟨W.executes.1, W.executes.2.1⟩, W.realizes,
    ⟨W.code, W.resources.retained, ⟨W.executes.1, W.executes.2.1⟩, W.realizes⟩⟩

/-- Add a representation certificate to an existing execution/storage witness.
The same finite code and the same physical experiment are retained. -/
def attachEncoding (F A)
    (W : (OneUseStorageObservedBackend.registration (State := State) native modelGame hAdvantage).object.Witness F A)
    (e : EncodingProfile State) (hEncoding : e.Certificate W.resources F) :
    (registration (State := State) native modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, ⟨W.resources, e⟩, ⟨W.executes.1, W.executes.2, hEncoding⟩, W.realizes,
    ⟨W.code, ⟨W.resources, e⟩, ⟨W.executes.1, W.executes.2, hEncoding⟩, W.realizes⟩⟩

@[simp] theorem forget_attach_code (F A)
    (W : (OneUseStorageObservedBackend.registration (State := State) native modelGame hAdvantage).object.Witness F A)
    (e : EncodingProfile State) (hEncoding : e.Certificate W.resources F) :
    (forgetEncoding native modelGame hAdvantage F A
      (attachEncoding native modelGame hAdvantage F A W e hEncoding)).code = W.code := rfl

@[simp] theorem forget_attach_resources (F A)
    (W : (OneUseStorageObservedBackend.registration (State := State) native modelGame hAdvantage).object.Witness F A)
    (e : EncodingProfile State) (hEncoding : e.Certificate W.resources F) :
    (forgetEncoding native modelGame hAdvantage F A
      (attachEncoding native modelGame hAdvantage F A W e hEncoding)).resources = W.resources := rfl

theorem witness_bound_polynomial (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A) :
    PolynomiallyBounded (W.resources.encoded.bound W.resources.retained native W.code) :=
  W.resources.encoded.bound_polynomial W.resources.retained native W.code F
    W.executes.2.2 W.executes.2.1 W.executes.1.1

theorem witness_encoded_peak (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A)
    (n : Nat) (side : Bool) (elapsed : Nat) (hElapsed : elapsed ≤ W.resources.retained.execution.horizon n)
    (target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen native W.code
        (W.resources.retained.execution.oracle n (F n) side) (W.resources.retained.execution.caller n (F n) side)) elapsed
      (.initializing (.generating
        (Machine.Configuration.initial (List.replicate (W.resources.retained.execution.width n) true))))).support) :
    ((PrivateControllerEncoding.completeEncoding W.resources.encoded.encoding).encode
      (Machine.OneTimePad.keygen, native, W.code,
        PrivateControllerEncoding.runtime (W.resources.retained.execution.caller n (F n) side) target)).length ≤
      W.resources.encoded.bound W.resources.retained native W.code n :=
  W.resources.encoded.encoded_peak W.resources.retained native W.code F W.executes.2.2 W.executes.2.1
    n side elapsed hElapsed target hTarget

theorem secure_of_logical (F : InstanceFamily P)
    (hSecure : ∀ (code : Code) (r : Resources P State),
      r.retained.execution.ExecutesWithin native F code →
      r.retained.storage.Certificate r.retained.execution F → r.encoded.Certificate r.retained F →
      Negligible (fun n =>
        probabilityGap (eventProb (r.retained.execution.logicalGame F code n false) (· = true))
          (eventProb (r.retained.execution.logicalGame F code n true) (· = true)))) :
    (registration (State := State) native modelGame hAdvantage).object.Secure F := by
  apply ObservedExecution.secure_of_native
  intro code r hExec
  have h := hSecure code r hExec.1 hExec.2.1 hExec.2.2
  change Negligible (fun n =>
    probabilityGap (eventProb (r.retained.execution.nativeGame native F code n false) (· = true))
      (eventProb (r.retained.execution.nativeGame native F code n true) (· = true)))
  simpa only [r.retained.execution.nativeGame_eq native F code hExec.1] using h

end CryptoLogic.General.OneUseEncodedObservedBackend
