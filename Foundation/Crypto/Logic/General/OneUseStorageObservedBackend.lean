import Foundation.Crypto.Logic.General.OneUseContractObservedBackend

/-! Attach complete retained-data bounds to the handler-independent native
registration. Counts are tape cells, retained bits/lists and the supplied
external-state measure, including transient copies and original inputs.
Integer program counters, finite-code bit encodings and host allocations
are not included in this measure. -/
namespace CryptoLogic.General.OneUseStorageObservedBackend
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive
open OneUseContractObservedBackend
universe u v
set_option backward.isDefEq.respectTransparency false

structure StorageProfile (State : Type v) where
  stateSize : State → Nat
  initialCap : Nat → Nat
  stateIncrement : Nat → Nat
  responseCap : Nat → Nat

namespace StorageProfile
variable {P : CryptoGoal.{u}} {State : Type v}
    (s : StorageProfile State) (r : OneUseContractObservedBackend.Profile P State)

structure Certificate (F : InstanceFamily P) : Prop where
  initialPolynomial : PolynomiallyBounded s.initialCap
  incrementPolynomial : PolynomiallyBounded s.stateIncrement
  responsePolynomial : PolynomiallyBounded s.responseCap
  initialBound : ∀ n side, ControllerExtent.initializationExtent s.stateSize (r.caller n (F n) side)
    (.initializing (.generating (Machine.Configuration.initial (List.replicate (r.width n) true)))) ≤ s.initialCap n
  oracleBound : ∀ n side state request result, result ∈ (r.oracle n (F n) side state request).support →
    s.stateSize result.1 ≤ s.stateSize state + s.stateIncrement n ∧ result.2.length ≤ s.responseCap n

def bound (n : Nat) : Nat :=
  4 * (s.initialCap n + r.horizon n * (s.stateIncrement n + s.responseCap n + 2)) ^ 2 +
  11 * (s.initialCap n + r.horizon n * (s.stateIncrement n + s.responseCap n + 2)) + 2

theorem bound_polynomial (F : InstanceFamily P) (hStorage : s.Certificate r F)
    (hTime : PolynomiallyBounded r.horizon) : PolynomiallyBounded (s.bound r) := by
  have hi := (hStorage.incrementPolynomial.add hStorage.responsePolynomial).add (PolynomiallyBounded.const 2)
  have he := hStorage.initialPolynomial.add (hTime.mul hi)
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 11).mul he)).add (PolynomiallyBounded.const 2)
  change PolynomiallyBounded (fun n =>
    4 * (s.initialCap n + r.horizon n * (s.stateIncrement n + s.responseCap n + 2)) ^ 2 +
    11 * (s.initialCap n + r.horizon n * (s.stateIncrement n + s.responseCap n + 2)) + 2)
  simpa only [pow_two] using hb

theorem memory_peak (native : Machine.Program) (F : InstanceFamily P)
    (code : CryptoOracle.Interactive.Code) (hStorage : s.Certificate r F)
    (n : Nat) (side : Bool) (elapsed : Nat) (hElapsed : elapsed ≤ r.horizon n)
    (target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen native code
        (r.oracle n (F n) side) (r.caller n (F n) side)) elapsed
      (.initializing (.generating (Machine.Configuration.initial (List.replicate (r.width n) true))))).support) :
    ControllerStorage.initializationCells s.stateSize (r.caller n (F n) side) target ≤ s.bound r n := by
  have hp := ControllerExtent.initialization_peak s.stateSize Machine.OneTimePad.keygen native code
    (r.oracle n (F n) side) (r.caller n (F n) side) (s.stateIncrement n) (s.responseCap n)
    (hStorage.oracleBound n side) (r.horizon n) elapsed hElapsed
    (.initializing (.generating (Machine.Configuration.initial (List.replicate (r.width n) true)))) target hTarget
  have he := Nat.add_le_add_right (hStorage.initialBound n side)
    (r.horizon n * (s.stateIncrement n + s.responseCap n + 2))
  have hq := Nat.pow_le_pow_left he 2
  exact hp.trans (Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left 4 hq) (Nat.mul_le_mul_left 11 he)) 2)

end StorageProfile

structure Resources (P : CryptoGoal.{u}) (State : Type v) where
  execution : OneUseContractObservedBackend.Profile P State
  storage : StorageProfile State

variable {P : CryptoGoal.{u}} {State : Type v}

noncomputable def registration (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true))) :
    ObservedExecution Backends.system .interactive P where
  Resources := Resources P State
  ExecutesWithin := fun F code r => r.execution.ExecutesWithin native F code ∧ r.storage.Certificate r.execution F
  game := fun F code r => r.execution.nativeGame native F code
  modelGame := modelGame
  advantage_eq := hAdvantage

variable (native : Machine.Program)
    (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

def witness (F A) (code : CryptoOracle.Interactive.Code) (r : Resources P State)
    (hExec : r.execution.ExecutesWithin native F code) (hStorage : r.storage.Certificate r.execution F)
    (hLogical : ∀ n side, r.execution.logicalGame F code n side = modelGame F A n side) :
    (registration (State := State) native modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration (State := State) native modelGame hAdvantage).Realizes F A code r := by
    intro n side
    exact (r.execution.nativeGame_eq native F code hExec n side).trans (hLogical n side)
  exact ⟨code, r, ⟨hExec, hStorage⟩, hReal, ⟨code, r, ⟨hExec, hStorage⟩, hReal⟩⟩

/-- Retaining a storage proof strengthens the represented class without
changing its emitted code, time profile, or observed experiment. -/
def forgetStorage (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A) :
    (OneUseContractObservedBackend.registration (State := State) native modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, W.resources.execution, W.executes.1, W.realizes,
    ⟨W.code, W.resources.execution, W.executes.1, W.realizes⟩⟩

theorem witness_bound_polynomial (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A) :
    PolynomiallyBounded (W.resources.storage.bound W.resources.execution) :=
  W.resources.storage.bound_polynomial W.resources.execution F W.executes.2 W.executes.1.1

theorem witness_memory_peak (F A)
    (W : (registration (State := State) native modelGame hAdvantage).object.Witness F A)
    (n : Nat) (side : Bool) (elapsed : Nat) (hElapsed : elapsed ≤ W.resources.execution.horizon n)
    (target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval
      (OneUseInitialization.step Machine.OneTimePad.keygen native W.code
        (W.resources.execution.oracle n (F n) side) (W.resources.execution.caller n (F n) side)) elapsed
      (.initializing (.generating
        (Machine.Configuration.initial (List.replicate (W.resources.execution.width n) true))))).support) :
    ControllerStorage.initializationCells W.resources.storage.stateSize
      (W.resources.execution.caller n (F n) side) target ≤
        W.resources.storage.bound W.resources.execution n :=
  W.resources.storage.memory_peak W.resources.execution native F W.code W.executes.2 n side elapsed hElapsed target hTarget

end CryptoLogic.General.OneUseStorageObservedBackend
