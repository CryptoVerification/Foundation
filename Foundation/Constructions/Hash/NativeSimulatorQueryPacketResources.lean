import Foundation.Constructions.Hash.NativeSimulatorQueryPacket
import Foundation.Crypto.Semantics.Oracle.NativePacketCodeResources

/-! Faithful storage bounds for the entire physical request/lookup/update/
export controller, including the pre-admission frame and every working tape. -/
namespace Foundation.Hash.Native.SimulatorQueryPacket
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def encodingView {State : Type*} : Control State → Bool × NativePacketComponent.Control State
  | .admitting state machine trace request => (false, .computing ⟨state, .loading machine request {}, trace⟩)
  | .running component => (true, component)

def controlEncoding {State : Type*} (E : FiniteBitEncoding State) : FiniteBitEncoding (Control State) where
  encode := fun control => (Machine.ConfigurationEncoding.bit.prod (NativePacketComponent.Resources.encoding E)).encode (encodingView control)
  decode := fun raw => do
    let (tag, component) ← (Machine.ConfigurationEncoding.bit.prod (NativePacketComponent.Resources.encoding E)).decode raw
    if tag then some (.running component) else
      match component with
      | .computing ⟨state, .loading machine request _, trace⟩ => some (.admitting state machine trace request)
      | _ => none
  decode_encode := by
    intro control
    cases control <;> simp [encodingView, FiniteBitEncoding.decode_encode]

def fullEncoding {State : Type*} (E : FiniteBitEncoding State) := EncodedStorage.codeEncoding.prod (controlEncoding E)

theorem running_encoding_length {State : Type*} (E : FiniteBitEncoding State) (program : Code)
    (component : NativePacketComponent.Control State) :
    ((fullEncoding E).encode (program, Control.running component)).length =
      ((NativePacketComponent.fullEncoding E).encode (program, component)).length + 3 := by
  simp [fullEncoding, controlEncoding, encodingView, NativePacketComponent.fullEncoding,
    FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit]
  omega

theorem after_admission_run {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (request : List Bool) (fuel : Nat) :
    TimedExecution.eval (step n κ oracle) (fuel + 1) (.admitting state machine trace request) =
      (TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) fuel
        (.computing (SimulatorQueryLoading.loadingFrame n κ state machine trace request))).map Control.running := by
  change ((step n κ oracle (.admitting state machine trace request)).bind _) = _
  rw [step, PMF.pure_bind, running_run]

def storageBound {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (n κ : Nat) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool) (horizon : Nat) : Nat :=
  max (((fullEncoding E).encode (code n κ, Control.admitting state machine trace request)).length)
    (NativePacketComponent.storageBound (code n κ)
      (NativePacketComponent.Resources.frameSize stateSize (SimulatorQueryLoading.loadingFrame n κ state machine trace request)) horizon + 3)

/-- No request validity or terminal-recognition assumption is needed for
storage. The unused external oracle is arbitrary. Actual represented cells
and both the retained frame and exporter working state are counted. -/
theorem encoded_peak {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    {n κ : Nat} (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (horizon elapsed : Nat) (within : elapsed ≤ horizon + 1) (target : Control State)
    (support : target ∈ (TimedExecution.eval (step n κ oracle) elapsed
      (.admitting state machine trace request)).support) :
    ((fullEncoding E).encode (code n κ, target)).length ≤
      storageBound E stateSize n κ state machine trace request horizon := by
  cases elapsed with
  | zero =>
      rw [TimedExecution.eval, PMF.mem_support_pure_iff] at support
      subst target
      exact Nat.le_max_left _ _
  | succ elapsed =>
      rw [after_admission_run, PMF.mem_support_map_iff] at support
      obtain ⟨component, reachable, rfl⟩ := support
      have bound := NativePacketComponent.encoded_peak_from E stateSize hState oracle (code n κ)
        (SimulatorLookupDispatch.code_native n κ)
        (.computing (SimulatorQueryLoading.loadingFrame n κ state machine trace request))
        (by trivial) horizon elapsed (by omega) component reachable
      rw [running_encoding_length]
      exact (Nat.add_le_add_right bound 3).trans (Nat.le_max_right _ _)

theorem first_encoded {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    {n κ : Nat} (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (horizon : Nat) (result : Control State × Nat)
    (support : result ∈ (runToBoundary (step n κ oracle) readyBoundary (horizon + 1)
      (.admitting state machine trace request)).support) :
    ((fullEncoding E).encode (code n κ, result.1)).length ≤
      storageBound E stateSize n κ state machine trace request horizon :=
  encoded_peak E stateSize hState oracle state machine trace request horizon result.2
    (runToBoundary_bounded _ _ _ _ result support) result.1
    (runToBoundary_reachable _ _ _ _ result support)

end Foundation.Hash.Native.SimulatorQueryPacket
